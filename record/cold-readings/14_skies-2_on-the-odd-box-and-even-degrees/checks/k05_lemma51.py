# k05_lemma51.py -- Grepy Skies 2. Gate for Lemma 5.1 of PROOF_ODD_BOX.md.
#  (M1) Pf_{E_l}(M) in U_l(M) = ( Delta(S) D_Q : |S| = l+1, Q perfect matching of M \ S ), over F_p,
#       with the Pfaffian computed from its definition (recursive expansion of the bordered matrix).
#  (M2) the dictionary: Pf_E(M) = +- sum_X sgn(X) det(y_X^E) Pf_B(y_{X^c})   (F7 against (5.1)), over Z.
#  (M3) Pf_{E_l}(M) = 0 when l + t > h (Remark (2)).
#  (M4) the identity of Remark (4): gamma_2(J_{h-1}) = - sum_{j>=1} J_{h-1-j} ^ J_{h-1+j}, as polynomials over Z.
#  controls that can fail: wrong border set; a sub-family of the generators of U.
# usage: python3 k05_lemma51.py r "l,t l,t ..." p1,p2,...
import sys, time, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import *

r = int(sys.argv[1]); cases = [tuple(int(x) for x in c.split(',')) for c in sys.argv[2].split()]
primes = [int(x) for x in sys.argv[3].split(',')]
h = (r - 1) // 2

def perm_sign(seq):
    s = 1; seq = list(seq)
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]: s = -s
    return s

def alternant(n, X, E, r):
    """det(y_i^{e_k}), i in X (sorted), e in E (sorted)."""
    X = list(X); E = list(E)
    tot = {}
    for perm in itertools.permutations(range(len(E))):
        f = one(n)
        for i, pk in zip(X, perm):
            f = pmul(f, mono(n, i, E[pk], r), r)
        tot = padd(tot, f, perm_sign(perm))
    return tot

def omega(n, a, b, s, r):
    """omega_s(y_a,y_b) = sum_{u+u'=s, 0<=u,u'<=r-1} (-1)^u y_a^u y_b^{u'}"""
    c = {}
    for u in range(r):
        u2 = s - u
        if 0 <= u2 <= r - 1:
            k = [0] * n; k[a] += u; k[b] += u2
            c[tuple(k)] = (-1) ** u
    return c

def Ugens(n, M, l, r, skipS=None):
    g = []
    for Sset in itertools.combinations(M, l + 1):
        if skipS is not None and Sset == skipS: continue
        rest = [x for x in M if x not in Sset]
        dl = vdm(n, Sset, r)
        for Q in matchings(rest):
            f = dl
            for (a, b) in Q: f = pmul(f, Dpoly(n, a, b, r), r)
            if f: g.append(f)
    return g

print("r=%d h=%d" % (r, h))
for (l, t) in cases:
    t0 = time.time()
    n = l + 1 + 2 * t
    M = list(range(n))
    E = E_l(l, r)
    PF = bordered_pf(n, M, E, r)
    # (M2) dictionary
    s = len(E); wedge = {}
    for X in itertools.combinations(M, s):
        Xc = [x for x in M if x not in X]
        sg = perm_sign(list(X) + Xc)
        pfB = bordered_pf(n, Xc, [], r)
        wedge = padd(wedge, pmul(alternant(n, X, E, r), pfB, r), sg)
    dict_ok = (PF == wedge) or (PF == pscal(wedge, -1))
    line = " (l,t)=(%d,%d) n=%d: Pf has %d terms, degree %s; dictionary (F7)=(5.1) up to a global sign: %s" % (
        l, t, n, len(PF), deg(PF), dict_ok)
    if l + t > h:
        print(line + "; l+t>h, (M3) Pf == 0: %s" % (not PF))
        continue
    print(line)
    G = Ugens(n, M, l, r)
    # wrong borders for the control
    Ebad = [r - 2] if l == 0 else list(range(1, l))
    PFbad = bordered_pf(n, M, Ebad, r)
    for p in primes:
        I = ideal(G, n, r, p, maxdeg=deg(PF))
        ok = member(PF, I, n, r, p)
        zero_mod_p = not {k: v % p for k, v in PF.items() if v % p}
        okbad = (member(PFbad, ideal(G, n, r, p, maxdeg=deg(PFbad)), n, r, p) if PFbad else None)
        # control: drop the generators with one fixed S
        S0 = tuple(M[:l + 1])
        I2 = ideal(Ugens(n, M, l, r, skipS=S0), n, r, p, maxdeg=deg(PF))
        ok2 = member(PF, I2, n, r, p)
        print("   p=%d (M1) Pf_{E_l}(M) in U_l(M): %s%s | control wrong borders %s in U: %s | control U without the S={%s} generators: %s  [%d gens, %.1fs]"
              % (p, ok, " (Pf = 0 mod p)" if zero_mod_p else "", Ebad, okbad, ",".join(map(str, S0)), ok2, len(G), time.time() - t0))

# (M4) Remark (4): gamma_2(J_{h-1}) = - sum_{j>=1} J_{h-1-j} ^ J_{h-1+j}, on 4 variables
if h >= 1:
    n = 4
    lhs = bordered_pf(n, [0, 1, 2, 3], [], r)          # Pf(B) on 4 variables = gamma_2(J_{h-1})
    rhs = {}
    for j in range(1, h + 1):
        s1 = 2 * (h - 1 - j) + 1; s2 = 2 * (h - 1 + j) + 1
        if s1 < 1 or s2 > 2 * r - 3: continue
        # wedge of two 2-forms: sum over X (2-subsets) sgn * f(y_X) g(y_Xc)
        for X in itertools.combinations(range(4), 2):
            Xc = [x for x in range(4) if x not in X]
            sg = perm_sign(list(X) + Xc)
            rhs = padd(rhs, pmul(omega(n, X[0], X[1], s1, r), omega(n, Xc[0], Xc[1], s2, r), r), sg)
    print(" (M4) gamma_2(J_{h-1}) = - sum_j J_{h-1-j}^J_{h-1+j} over Z: %s   (and with the wrong sign: %s)"
          % (lhs == pscal(rhs, -1), lhs == rhs))
    # pair forms: omega_{r-2} = B, omega_{r-1+i} = b^i D mod the box (i odd)
    okB = omega(2, 0, 1, r - 2, r) == Bpoly(2, 0, 1, r)
    okD = all(omega(2, 0, 1, r - 1 + i, r) == pmul(mono(2, 1, i, r), Dpoly(2, 0, 1, r), r) for i in range(1, r - 1, 2))
    print(" (5.4) omega_{r-2} = B: %s ; omega_{r-1+i} = b^i D mod box for odd i: %s" % (okB, okD))
