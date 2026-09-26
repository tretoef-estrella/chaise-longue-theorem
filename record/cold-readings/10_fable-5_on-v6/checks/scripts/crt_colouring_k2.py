"""
crt_colouring_k2.py — dim_{F_p} (psi_J : J in J) F_p[G] for a Fermat variety of dimension n = 2k (default k = 2,
n+1 = 5 variables) and composite odd degree m = q*r, q = p^v, p ∤ r, computed from the LITERAL generators of
Degtyarev–Shimada (source line 326):  psi_J = prod_{i=0}^{k}(t_{k_i}-1) * prod_{i=1}^{k} phi(t_{j_i}t_{k_i}).

Method (only the Chinese remainder theorem, nothing from §6 of the paper):
  over F = F_{p^d} ⊇ μ_r (d = ord_r(p)),  t^m - 1 = (t^r - 1)^q = prod_{ζ∈μ_r} (t-ζ)^q,  so
  F[t]/(t^m-1) ≅ prod_ζ F[t]/((t-ζ)^q)   and   F[G] ≅ prod_{c ∈ μ_r^{n+1}} R_c,  R_c = F[u_1..u_{n+1}]/(u_i^q), u_i = t_i - c_i.
  For any ideal I = (g_1..g_s):  dim_F I = Σ_c dim_F (π_c(g_1), .., π_c(g_s)) R_c,  and dim_F = dim_{F_p} since the g's
  have F_p-coefficients.  In each R_c the images π_c(psi_J) are computed by substituting t_i = c_i + u_i and truncating
  (u_i^q = 0); the ideal they generate is closed under multiplication by the u_i and its dimension is measured by exact
  linear algebra over F (gf_linalg.Span).
Symmetries (optional, to save time; each is a ring automorphism of F[G] permuting the R_c and fixing the ideal I):
  - Frobenius x ↦ x^p on coefficients (fixes psi_J, has F_p coefficients), sends R_c to R_{c^p};
  - permutations of t_1..t_{n+1}: psi_J ↦ (unit)·psi_{π(J)} because (t_b-1)phi(t_a t_b) = -t_a^{-1}(t_a-1)phi(t_a t_b)
    (use u = t_a t_b and u·phi(u) = phi(u) in F[G]); index 0 is fixed.
  The option --sym none computes every colouring; --sym galois uses Frobenius orbits; --sym full uses both.
  A random sample of colourings can be recomputed without symmetry (--audit N) to check the orbit values.

usage: python3 crt_colouring_k2.py m p [--k 2] [--sym none|galois|full] [--audit N] [--only-orbits a:b]
Prediction to compare with: Q_k(m) = N!·[x^N] I_0(2x)^{(m-1)/2}, N = 2k+2  (paper: 32 900 at m=15, 102 800 at m=21, k=2).
"""
import sys, time, itertools, argparse, random
from math import comb, factorial
from fractions import Fraction
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gf_linalg import GF, Span

def Qk(k, m):
    """N!·[x^N] I_0(2x)^h with h=(m-1)/2, I_0(2x) = Σ x^{2b}/(b!)^2"""
    N = 2 * k + 2; h = (m - 1) // 2
    # coefficient of x^N in (Σ_b x^{2b}/b!^2)^h : sum over compositions of N/2 into h parts
    tot = Fraction(0)
    def rec(parts_left, remaining, acc):
        nonlocal tot
        if parts_left == 0:
            if remaining == 0:
                tot += acc
            return
        for b in range(remaining + 1):
            rec(parts_left - 1, remaining - b, acc / Fraction(factorial(b)) ** 2)
    rec(h, N // 2, Fraction(1))
    return int(tot * factorial(N))

def matchings(N):
    idx = list(range(N))
    def rec(rest):
        if not rest:
            yield []; return
        a = rest[0]
        for b in rest[1:]:
            r2 = [x for x in rest if x not in (a, b)]
            for mm in rec(r2):
                yield [(a, b)] + mm
    return list(rec(idx))

def ord_mod(p, r):
    d = 1; x = p % r
    while x != 1:
        x = (x * p) % r; d += 1
    return d

class Engine:
    def __init__(self, m, p, k):
        self.m, self.p, self.k = m, p, k
        q = p
        while m % (q * p) == 0:
            q *= p
        self.q = q; self.r = m // q
        assert self.r % p != 0
        self.nvar = 2 * k + 1; self.N = 2 * k + 2
        self.d = ord_mod(p, self.r) if self.r > 1 else 1
        self.gf = GF(p, self.d)
        self.zeta = self.gf.primitive_root_of_unity(self.r) if self.r > 1 else 1
        self.Js = matchings(self.N)
        # binomials mod p
        self.binom = [[comb(e, a) % p for a in range(q)] for e in range(m)]
        # powers of zeta
        self.zpow = [self.gf.power(self.zeta, e) for e in range(self.r)]
        self.dimR = q ** self.nvar

    # --- scalar field ops ---
    def fmul(self, a, b): return int(self.gf.mul[a, b])
    def fadd(self, a, b): return int(self.gf.add[a, b])
    def fsub(self, a, b): return int(self.gf.sub[a, b])

    def factor_single(self, c):
        """(t - 1) with t = c + u: array of length q over F"""
        q = self.q; f = np.zeros(q, dtype=np.int64)
        f[0] = self.fsub(c, 1); f[1] = 1 if q > 1 else 0
        return f

    def factor_pair(self, cj, ck):
        """(t_k - 1)·phi(t_j t_k) with t = c + u, as a q x q array (axis 0 = u_j, axis 1 = u_k) over F"""
        q, m, gf = self.q, self.m, self.gf
        # powers of cj, ck
        cjp = [1] * (m + 1); ckp = [1] * (m + 1)
        for e in range(1, m + 1):
            cjp[e] = self.fmul(cjp[e - 1], cj); ckp[e] = self.fmul(ckp[e - 1], ck)
        phi = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                s = 0
                for e in range(m):
                    if e < a or e < b:
                        continue
                    coef = (self.binom[e][a] * self.binom[e][b]) % self.p  # in F_p ⊂ F
                    if coef == 0:
                        continue
                    term = self.fmul(self.fmul(coef, cjp[e - a]), ckp[e - b])
                    s = self.fadd(s, term)
                phi[a, b] = s
        # multiply by (t_k - 1) = (ck - 1) + u_k
        out = np.zeros((q, q), dtype=np.int64)
        ck1 = self.fsub(ck, 1)
        mulv = gf.mul
        out = mulv[ck1, phi].astype(np.int64)
        # + u_k * phi : shift along axis 1
        shifted = np.zeros_like(phi); shifted[:, 1:] = phi[:, :-1]
        out = gf.add[out, shifted].astype(np.int64)
        return out

    def image_psi(self, J, c):
        """image of psi_J in R_c as a (q,)*nvar array (int-encoded field elements); c = tuple of colours c_1..c_{n+1}"""
        q, nvar = self.q, self.nvar
        # tensor factors on disjoint axes
        factors = []  # (axes, array)
        for (j, kk) in J:
            if j == 0:
                factors.append(((kk - 1,), self.factor_single(c[kk - 1])))
            else:
                factors.append(((j - 1, kk - 1), self.factor_pair(c[j - 1], c[kk - 1])))
        # build full array by successive outer products over F: since we cannot use np.multiply.outer with a table
        # directly, do it with einsum over components? simpler: iterate. Start with scalar 1.
        arr = np.array(1, dtype=np.int64); axes_done = []
        for axes, fac in factors:
            # outer product via table lookups: new[..., a, b] = mul[arr[...], fac[a,b]]
            arr = self.gf.mul[arr.reshape(arr.shape + (1,) * fac.ndim), fac.reshape((1,) * arr.ndim + fac.shape)].astype(np.int64)
            axes_done += list(axes)
        # now arr has axes in order axes_done; transpose to variable order 0..nvar-1
        perm = [axes_done.index(i) for i in range(nvar)]
        arr = np.transpose(arr, perm)
        return arr

    def ideal_dim(self, c, verbose=False):
        q, nvar = self.q, self.nvar
        gens = []
        for J in self.Js:
            g = self.image_psi(J, c)
            if g.any():
                gens.append(g.reshape(-1))
        if not gens:
            return 0, 0
        S = Span(self.gf, self.dimR, batch=64)
        frontier = S.add(np.array(gens, dtype=self.gf.dtype))
        rounds = 0
        while frontier.shape[0]:
            rounds += 1
            F = frontier.reshape((-1,) + (q,) * nvar)
            new = []
            for i in range(nvar):
                sh = np.zeros_like(F)
                sl_src = [slice(None)] * (nvar + 1); sl_dst = [slice(None)] * (nvar + 1)
                sl_src[i + 1] = slice(0, q - 1); sl_dst[i + 1] = slice(1, q)
                sh[tuple(sl_dst)] = F[tuple(sl_src)]
                new.append(sh.reshape(F.shape[0], -1))
            new = np.vstack(new)
            # drop zero rows
            nzr = new.any(axis=1)
            new = new[nzr]
            frontier = S.add(new) if new.shape[0] else new[:0]
        return S.dim(), len(gens)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('m', type=int); ap.add_argument('p', type=int)
    ap.add_argument('--k', type=int, default=2)
    ap.add_argument('--sym', default='full', choices=['none', 'galois', 'full'])
    ap.add_argument('--audit', type=int, default=0, help='recompute N random colourings without symmetry and compare')
    ap.add_argument('--only-orbits', default=None, help='a:b slice of the orbit list (for splitting runs)')
    ap.add_argument('--seed', type=int, default=12345)
    a = ap.parse_args()
    m, p, k = a.m, a.p, a.k
    E = Engine(m, p, k)
    r, q, d = E.r, E.q, E.d
    Qpred = Qk(k, m)
    print(f"m={m}={q}*{r} p={p} k={k} nvar={E.nvar}: F=GF({p}^{d}) (poly {E.gf.poly}), zeta of order {r}; block dim q^nvar={E.dimR}; "
          f"#colourings r^nvar={r**E.nvar}; PREDICTION Σ_c dim = Q_{k}({m}) = {Qpred}, quotient {m**E.nvar - Qpred}")
    t0 = time.time()
    # colourings as exponent tuples e in (Z/r)^nvar, c_i = zeta^{e_i}
    allc = list(itertools.product(range(r), repeat=E.nvar))
    def canon(e):
        e = tuple(e)
        if a.sym == 'none':
            return e
        cands = []
        x = e
        for _ in range(d):  # Frobenius orbit: e -> p e mod r
            y = x
            if a.sym == 'full':
                y = tuple(sorted(x))
            cands.append(y)
            x = tuple((p * v) % r for v in x)
        return min(cands)
    orbits = {}
    for e in allc:
        orbits.setdefault(canon(e), []).append(e)
    reps = sorted(orbits)
    print(f"#orbits (sym={a.sym}) = {len(reps)}")
    if a.only_orbits:
        lo, hi = [int(x) for x in a.only_orbits.split(':')]
        reps = reps[lo:hi]
        print(f"processing orbits {lo}:{hi} only (partial sum!)")
    total = 0; nonzero = 0; ncol_nonzero = 0
    results = {}
    for idx, rep in enumerate(reps):
        c = tuple(E.zpow[v] for v in rep)
        dim, ng = E.ideal_dim(c)
        mult = len(orbits[rep])
        results[rep] = dim
        total += dim * mult
        if dim:
            nonzero += 1; ncol_nonzero += mult
        if dim or idx % 50 == 0:
            print(f"  orbit {idx}/{len(reps)} rep={rep} mult={mult} surviving gens={ng} dim={dim}  (running total {total}, {time.time()-t0:.1f}s)", flush=True)
    print(f"TOTAL Σ_c dim π_c(I) = {total}  over {ncol_nonzero} colourings with non-zero image ({nonzero} orbits); prediction {Qpred}: "
          f"{'AGREES' if total == Qpred else 'DISAGREES'}  [{time.time()-t0:.1f}s]")
    if a.audit:
        rng = random.Random(a.seed)
        sample = rng.sample(allc, a.audit)
        bad = 0
        for e in sample:
            c = tuple(E.zpow[v] for v in e)
            dim, ng = E.ideal_dim(c)
            rep = canon(e)
            ok = (rep in results) and results[rep] == dim
            if not ok:
                bad += 1
            print(f"  audit e={e} dim={dim} orbit-rep={rep} orbit-dim={results.get(rep)} {'ok' if ok else 'MISMATCH'}")
        print(f"AUDIT: {a.audit} random colourings recomputed without symmetry, {bad} mismatches  [{time.time()-t0:.1f}s]")

if __name__ == '__main__':
    main()
