"""
headline_claim43_and_lemma22.py  (referee sub-task: THE HEADLINE CHAIN)

Two joints of the proof of the Main Theorem for composite odd m that no earlier log tests.

(A) Theorem 0(b) = [DS, Claim 4.3] at COMPOSITE m for a prime ell NOT dividing m.
    The paper's Proposition 2.1 needs rho = rank A_J = m^{n+1} - |Gamma_J| (from Claim 4.3 at p = 0) and
    Theorem 0(d) (no ell-torsion for ell not dividing m) -- both are statements at primes/characteristics
    ell with ell not dividing m, and neither was exercised by the earlier literal_k1 runs (which assert p | m).
    Here: the literal generators of [DS] (source line 326), psi_J = (t_{k0}-1)(t_{k1}-1) phi(t_{j1} t_{k1}),
    in F_ell[t_1,t_2,t_3]/(t_i^m - 1) (k = 1, n+1 = 3), and dim_{F_ell} of the ideal they generate.
    Prediction: dim (psi_J) = |Gamma_J| = Q_1(m) = 3(m-1)(m-2) for EVERY prime ell not dividing m
    (Claim 4.3 over F_ell-bar plus flat base change), so dim F_ell[G]/(psi_J) = m^3 - Q_1(m).
    Spanning set of the ideal (psi_J): mode 'reduced' uses t_{k0}^a t_{k1}^b psi_J, 0 <= a, b <= m-2.
    Justification (independent of the paper): t_{j1} t_{k1} phi(t_{j1} t_{k1}) = phi(t_{j1} t_{k1}) gives
    t_{j1} psi_J = t_{k1}^{-1} psi_J, so every t^nu psi_J is t_{k0}^a t_{k1}^b psi_J; and (t-1) phi(t) = 0
    with (t_{k0}-1) | psi_J, (t_{k1}-1) | psi_J gives t^{m-1} psi_J = -(1 + ... + t^{m-2}) psi_J for
    t = t_{k0}, t_{k1}.  Mode 'all' uses every translate t^nu psi_J (no argument needed) as a control.

(B) Lemma 2.2 for composite odd m at k = 2 (n+1 = 5 coordinates), straight from [DS, Definition 1.3]:
    Gamma_J = { a in (mu_m \ 1)^5 : exists J in J (15 matchings) with a_{j_i} a_{k_i} = 1, i = 1, 2 }.
    Prediction: |Gamma_J| = Q_2(m) = 6! [x^6] I_0(2x)^{(m-1)/2} = 15 m^3 - 90 m^2 + 175 m - 100
    (paper §3 / [DS, Remark 4.4]); at m = 15: 32 900 (the number the paper reports in §12.3).
    Negative control (even m, k = 1): the count "N-tuples in mu_m \ 1 closed under inversion, determined by
    the last n+1 entries" is NOT |Gamma_J| when m is even (the fixed point -1 of inversion), while
    "splits into inverse pairs" is.  This isolates the one place where Lemma 2.2 uses that m is odd.

Everything below is written from scratch (own modular RREF); nothing is imported from the other scripts.
Predicted resources: < 100 MB, < 60 s.
"""
import sys, time, itertools
import numpy as np

# ---------------------------------------------------------------- modular linear algebra (own code)
class Echelon:
    """incremental reduced row echelon basis over F_ell (ell prime, small)"""
    def __init__(self, ell, ncols):
        self.ell = ell; self.n = ncols
        self.B = np.zeros((0, ncols), dtype=np.int32); self.piv = []

    def add(self, N):
        ell = self.ell
        N = np.asarray(N, dtype=np.int32) % ell
        if self.B.shape[0]:
            N = (N - (N[:, self.piv] @ self.B) % ell) % ell           # reduce against the basis
        # eliminate inside the batch
        rows = []; pivs = []
        for r in N:
            r = r.copy()
            for (pr, pc) in zip(rows, pivs):
                if r[pc]:
                    r = (r - r[pc] * pr) % ell
            nz = np.flatnonzero(r)
            if nz.size == 0:
                continue
            c = int(nz[0]); inv = pow(int(r[c]), ell - 2, ell)
            r = (r * inv) % ell
            for i in range(len(rows)):                               # keep the batch reduced
                if rows[i][c]:
                    rows[i] = (rows[i] - rows[i][c] * r) % ell
            rows.append(r); pivs.append(c)
        if rows:
            Nn = np.array(rows, dtype=np.int32)
            if self.B.shape[0]:
                self.B = (self.B - (self.B[:, pivs] @ Nn) % ell) % ell   # keep the old basis reduced
            self.B = np.vstack([self.B, Nn]); self.piv += pivs

    def dim(self):
        return self.B.shape[0]

# ---------------------------------------------------------------- the generators of [DS], k = 1
def matchings(N):
    def rec(rest):
        if not rest:
            yield []; return
        a = rest[0]
        for b in rest[1:]:
            for mm in rec([x for x in rest if x not in (a, b)]):
                yield [(a, b)] + mm
    return list(rec(list(range(N))))

def psi_dense(J, m, nvar):
    """psi_J as an array of shape (m,)*nvar over Z; variable i (1..nvar) is axis i-1"""
    f = np.zeros((m,) * nvar, dtype=np.int64); f[(0,) * nvar] = 1
    def mul_t(g, i, c=1):
        return np.roll(g, c, axis=i - 1)
    for (j, k) in J:                       # pairs sorted so that the first contains 0
        f = mul_t(f, k) - f                # (t_k - 1)
        if j != 0:
            g = np.zeros_like(f)
            for c in range(m):
                g += mul_t(mul_t(f, j, c), k, c)
            f = g                          # * phi(t_j t_k)
    return f

def ideal_dim_k1(m, ell, mode):
    nvar = 3
    E = Echelon(ell, m ** nvar)
    for J in matchings(4):
        f = psi_dense(J, m, nvar) % ell
        k0 = J[0][1]; (j1, k1) = J[1]
        rows = []
        if mode == 'reduced':
            for a in range(m - 1):
                ga = np.roll(f, a, axis=k0 - 1)
                for b in range(m - 1):
                    rows.append(np.roll(ga, b, axis=k1 - 1).reshape(-1))
                    if len(rows) >= 100:
                        E.add(np.array(rows)); rows = []
        else:
            for nu in itertools.product(range(m), repeat=nvar):
                g = f
                for i, e in enumerate(nu):
                    if e:
                        g = np.roll(g, e, axis=i)
                rows.append(g.reshape(-1))
                if len(rows) >= 400:
                    E.add(np.array(rows)); rows = []
        if rows:
            E.add(np.array(rows))
    return E.dim()

# ---------------------------------------------------------------- Gamma_J from Definition 1.3, and the counts
def Q_closed_form(k, m):
    # Q_k(m) = N! [x^N] I_0(2x)^h, N = 2k+2, h = (m-1)/2, exact rational arithmetic
    from fractions import Fraction
    from math import factorial
    N = 2 * k + 2; h = (m - 1) // 2
    # coefficients of I_0(2x) up to x^N
    I0 = [Fraction(0)] * (N + 1)
    for b in range(N // 2 + 1):
        I0[2 * b] = Fraction(1, factorial(b) ** 2)
    P = [Fraction(1)] + [Fraction(0)] * N
    for _ in range(h):
        Q = [Fraction(0)] * (N + 1)
        for i in range(N + 1):
            if P[i]:
                for j in range(N + 1 - i):
                    Q[i + j] += P[i] * I0[j]
        P = Q
    return int(P[N] * factorial(N))

def gamma_size_def13(m, k):
    """|Gamma_J| by [DS, Definition 1.3]: a in (mu_m \ 1)^{n+1}, exists J with a_{j_i} a_{k_i} = 1 (i >= 1)."""
    nvar = 2 * k + 1
    Js = matchings(2 * k + 2)
    # exponents 1..m-1 (a_i = zeta^{e_i}); condition a_j a_k = 1  <=>  e_j + e_k = 0 mod m
    grids = np.meshgrid(*([np.arange(1, m)] * nvar), indexing='ij')
    E = np.stack([g.reshape(-1) for g in grids], axis=1)      # rows = tuples, columns = e_1..e_{n+1}
    e0 = (-E.sum(axis=1)) % m                                    # exponent of a_0
    full = np.concatenate([e0[:, None], E], axis=1)              # columns 0..n+1
    ok = np.zeros(E.shape[0], dtype=bool)
    for J in Js:
        cond = np.ones(E.shape[0], dtype=bool)
        for (j, kk) in J[1:]:
            cond &= ((full[:, j] + full[:, kk]) % m) == 0
        ok |= cond
    return int(ok.sum()), E.shape[0]

def closed_under_inversion_count(m, k):
    """# of (n+1)-tuples in mu_m \ 1 such that the N-multiset (with a_0) is closed under inversion"""
    nvar = 2 * k + 1
    grids = np.meshgrid(*([np.arange(1, m)] * nvar), indexing='ij')
    E = np.stack([g.reshape(-1) for g in grids], axis=1)
    e0 = (-E.sum(axis=1)) % m
    full = np.concatenate([e0[:, None], E], axis=1)
    # multiplicity of residue c and of -c must agree for every c (closed under inversion); a_0 != 1 too
    cnt = np.zeros((E.shape[0], m), dtype=np.int8)
    for col in range(full.shape[1]):
        np.add.at(cnt, (np.arange(E.shape[0]), full[:, col]), 1)
    closed = np.ones(E.shape[0], dtype=bool)
    for c in range(m):
        closed &= cnt[:, c] == cnt[:, (-c) % m]
    closed &= cnt[:, 0] == 0
    # "splits into inverse pairs": closed AND the multiplicity of every self-inverse residue (c = -c mod m, c != 0) is even
    pairs = closed.copy()
    for c in range(1, m):
        if (2 * c) % m == 0:
            pairs &= cnt[:, c] % 2 == 0
    return int(closed.sum()), int(pairs.sum())

def main():
    t0 = time.time()
    print("== (A) Theorem 0(b) / [DS, Claim 4.3] at composite m, prime ell NOT dividing m (k = 1, literal psi_J) ==")
    cells = [(9, 2, 'all'), (9, 2, 'reduced'), (9, 5, 'reduced'),
             (15, 2, 'reduced'), (15, 2, 'all'), (15, 7, 'reduced'),
             (21, 2, 'reduced')]
    bad = 0
    for (m, ell, mode) in cells:
        assert m % ell != 0
        Q = 3 * (m - 1) * (m - 2)
        t1 = time.time()
        d = ideal_dim_k1(m, ell, mode)
        verdict = 'AGREES' if d == Q else 'DISAGREES'
        bad += (d != Q)
        print(f"  m={m} ell={ell} ({mode}): dim_F_ell (psi_J) = {d}, quotient {m**3 - d}; predicted Q_1(m) = {Q}, "
              f"quotient {m**3 - Q}: {verdict}  [{time.time()-t1:.1f}s]")
    print(f"RESULT (A): {'all agree' if bad == 0 else str(bad) + ' DISAGREEMENTS'}")

    print("== (B) Lemma 2.2 at composite odd m from [DS, Definition 1.3] (k = 2 and k = 1) ==")
    for (m, k) in [(15, 1), (21, 1), (9, 2), (15, 2)]:
        t1 = time.time()
        g, tot = gamma_size_def13(m, k)
        Q = Q_closed_form(k, m)
        poly = (15 * m**3 - 90 * m**2 + 175 * m - 100) if k == 2 else 3 * (m - 1) * (m - 2)
        print(f"  (k,m)=({k},{m}): |Gamma_J| = {g} of {tot} tuples; Q_k(m) closed form = {Q}; polynomial = {poly}; "
              f"{'AGREES' if g == Q == poly else 'DISAGREES'}  [{time.time()-t1:.1f}s]")
    print("== (B') negative control: even m, k = 1 (where Lemma 2.2's 'closed under inversion' step needs m odd) ==")
    for m in [4, 6, 8]:
        g, _ = gamma_size_def13(m, 1)
        closed, pairs = closed_under_inversion_count(m, 1)
        ds = 3 * m**2 - 9 * m + 6 + (1 if m % 2 == 0 else 0)   # rank L(X) from [DS, Remark 4.4]; |Gamma| = rank - 1
        print(f"  m={m}: |Gamma_J| (Def 1.3) = {g}; [DS, Remark 4.4] rank-1 = {ds - 1}; "
              f"'closed under inversion' count = {closed}; 'splits into inverse pairs' count = {pairs}  "
              f"-> Def1.3 == pairs: {g == pairs}; Def1.3 == closed: {g == closed}")
    for m in [5, 7, 9]:
        g, _ = gamma_size_def13(m, 1)
        closed, pairs = closed_under_inversion_count(m, 1)
        print(f"  m={m} (odd): |Gamma_J| = {g}; closed = {closed}; pairs = {pairs}; all equal: {g == closed == pairs}")
    print(f"total elapsed {time.time()-t0:.1f}s")

if __name__ == '__main__':
    main()
