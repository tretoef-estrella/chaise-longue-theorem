# k08_roots_T3.py -- Grepy Skies 2.
# (a) Theorem O at root cells: dim (D_J : J) C_{2k+1} over F_p against N_r(2k+2).
# (b) Theorem T3 (PROOF_ODD_BOX.md section 8), r = 3: the ideals I(m,J) built from THEIR definition,
#     dim I(m,J) against |Z_J^{(m)}|, the slice containments of the proof (honest slices), and the comparison
#     with V_Lambda of Definition 4.1 for Lambda = {j <= J}.
# usage: python3 k08_roots_T3.py roots "k,r,p ..."   |   python3 k08_roots_T3.py T3 mmax p1,p2,...
import sys, itertools, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import *

if sys.argv[1] == 'roots':
    for cell in sys.argv[2].split():
        k, r, p = (int(x) for x in cell.split(','))
        t0 = time.time()
        n = 2 * k + 1
        DJ = []
        for P, rest in pair_sets(list(range(n)), k):
            f = one(n)
            for (a, b) in P: f = pmul(f, Dpoly(n, a, b, r), r)
            DJ.append(f)
        I = ideal(DJ, n, r, p)
        d = idim(I); N = Nr(r, 2 * k + 2)
        print("(k,r,p)=(%d,%d,%d): %d generators, dim (D_J) = %d, N_r(2k+2) = %d : %s  [%.1fs]"
              % (k, r, p, len(DJ), d, N, "EQUAL" if d == N else ("LESS  <<<<<" if d < N else "GREATER"), time.time() - t0), flush=True)
else:
    mmax = int(sys.argv[2]); primes = [int(x) for x in sys.argv[3].split(',')]
    r = 3
    def gensI(m, J, n=None, off=0):
        """generators of I(m,J) on the variables off..off+m-1 of a ring with n variables."""
        if n is None: n = m
        I = list(range(off, off + m))
        if J >= m: return [one(n)]
        out = []
        def DP(P):
            f = one(n)
            for (a, b) in P: f = pmul(f, Dpoly(n, a, b, r), r)
            return f
        if (m - J) % 2 == 0:
            for P, rest in pair_sets(I, (m - J) // 2): out.append(DP(P))
        elif J >= 1:
            for P, rest in pair_sets(I, (m - 1 - J) // 2):
                d = DP(P)
                for a, b in itertools.combinations(rest, 2):
                    out.append(pmul(padd(mono(n, b, 1, r), mono(n, a, 1, r), -1), d, r))
            for P, rest in pair_sets(I, (m + 1 - J) // 2): out.append(DP(P))
        else:   # J = 0, m odd
            for c in I:
                rest = [x for x in I if x != c]
                for P in matchings(rest): out.append(pmul(mono(n, c, 2, r), DP(P), r))
            for abc in itertools.combinations(I, 3):
                rest = [x for x in I if x not in abc]
                for P in matchings(rest): out.append(pmul(vdm(n, abc, r), DP(P), r))
        return [f for f in out if f]
    def Zc(m, J):
        return sum(1 for M in itertools.product((-1, 0, 1), repeat=m) if abs(sum(M)) <= J)
    for p in primes:
        t0 = time.time()
        bad_dim = eqn = gt = 0; bad_slice = nsl = 0; bad_def = 0; ncells = 0
        for m in range(1, mmax + 1):
            for J in range(0, m + 1):
                ncells += 1
                IJ = ideal(gensI(m, J), m, r, p)
                d = idim(IJ); z = Zc(m, J)
                if d < z: bad_dim += 1; print("   dim < |Z| at (m,J)=(%d,%d): %d < %d" % (m, J, d, z))
                elif d == z: eqn += 1
                else: gt += 1
                # comparison with Definition 4.1: Lambda = {(j) with mark (m-j) mod 2 : j <= J}
                Lam = frozenset(((((j,) if j else ()), (m - j) % 2)) for j in range(0, J + 1))
                dV = idim(ideal(V_gens(Lam, list(range(m)), m, r), m, r, p))
                if dV != d: bad_def += 1
                # slices
                W = slices(IJ, m, r)
                need = [(2, J + 1), (1, J), (0, J - 1)] if J >= 1 else [(2, 1)]
                for (j, Jp) in need:
                    if Jp < 0: continue
                    small = ideal(gensI(m - 1, Jp), m - 1, r, p) if m - 1 >= 1 else ideal([one(0)] if Jp >= 0 else [], 0, r, p)
                    nsl += 1
                    if not contained(small, W[j], m - 1, r, p): bad_slice += 1; print("   slice containment fails at (m,J)=(%d,%d), W_%d vs I(m-1,%d)" % (m, J, j, Jp))
        print("T3, p=%d, m <= %d: %d ideals I(m,J): dim<|Z|: %d, dim=|Z|: %d, dim>|Z|: %d ; slice containments tested %d, failures %d ; dim I(m,J) != dim V_Lambda(Def 4.1): %d  [%.1fs]"
              % (p, mmax, ncells, bad_dim, eqn, gt, nsl, bad_slice, bad_def, time.time() - t0), flush=True)
    # control: the wrong sign in D (unsigned y_a^2 + y_a y_b + y_b^2) in odd characteristic
    def gens_unsigned(m, J):
        out = []
        for P, rest in pair_sets(list(range(m)), (m - J) // 2):
            f = one(m)
            for (a, b) in P:
                f = pmul(f, {k: abs(v) for k, v in Dpoly(m, a, b, r).items()}, r)
            out.append(f)
        return out
    for (m, J) in [(3, 1), (5, 1)]:
        for p in primes:
            d = idim(ideal(gens_unsigned(m, J), m, r, p)); z = Zc(m, J)
            print("control: I(%d,%d) with the unsigned D, p=%d: dim = %d against |Z| = %d (%s)" % (m, J, p, d, z, "same" if d == z else "differs"))
