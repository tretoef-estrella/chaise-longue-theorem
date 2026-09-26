"""
literal_k1.py — fully literal computation of dim_{F_p} (psi_J : J in J) F_p[G] for k = 1 (Fermat SURFACES),
composite odd m, from the generators of Degtyarev–Shimada (arXiv:1405.4683v3, line 326 of the source):

    tau_J = prod_{i=0}^{d} (t_{k_i} - 1),   psi_J = tau_J * prod_{i=1}^{d} phi(t_{j_i} t_{k_i}),   phi(t) = t^{m-1}+...+1,
    J = [[j_0,k_0], ..., [j_d,k_d]], j_i < k_i, j_0 < ... < j_d (so j_0 = 0), indices {0,...,n+1}, n = 2d, d = k.

Ring: F_p[G] = F_p[t_1..t_{n+1}]/(t_i^m - 1), basis t^nu, nu in (Z/m)^{n+1}, NO Chinese remainder theorem,
no colourings, no blocks: the ideal is the span of all t^nu * psi_J (mode 'all'), or of a spanning set of
the image of multiplication by psi_J (mode 'reduced', which only uses t_j t_k phi(t_j t_k) = phi(t_j t_k)).

Expected (paper, Lemma 2.2 / Theorem 0(c) / [DS, Remark 4.4]): dim ideal = Q_1(m) = 3(m-1)(m-2), i.e.
dim F_p[G]/(psi_J) = m^3 - Q_1(m), for every prime p | m (this is Degtyarev's theorem [De14] at k = 1).

usage: python3 literal_k1.py m p [all|reduced]
"""
import sys, time, itertools
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gf_linalg import GF, Span

def matchings(N):
    """all perfect matchings of {0..N-1} as lists of (j,k) with j<k, sorted by j (so first pair contains 0)"""
    idx = list(range(N))
    def rec(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for b in rest[1:]:
            r2 = [x for x in rest if x not in (a, b)]
            for m in rec(r2):
                yield [(a, b)] + m
    return list(rec(idx))

def psi(J, m, nvar):
    """psi_J as a dense array of shape (m,)*nvar over Z (small ints); variable i (1..nvar) is axis i-1"""
    f = np.zeros((m,) * nvar, dtype=np.int64)
    f[(0,) * nvar] = 1  # the element 1
    def mul_t(g, i, c=1):  # multiply by t_i^c
        return np.roll(g, c, axis=i - 1)
    for (j, k) in J:
        f = mul_t(f, k) - f              # (t_k - 1)
        if j != 0:
            # phi(t_j t_k) = sum_{c=0}^{m-1} (t_j t_k)^c
            g = np.zeros_like(f)
            for c in range(m):
                g += mul_t(mul_t(f, j, c), k, c)
            f = g
    return f

def main():
    m = int(sys.argv[1]); p = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'reduced'
    assert m % 2 == 1 and m % p == 0
    k = 1; nvar = 2 * k + 1; N = 2 * k + 2
    Q = 3 * (m - 1) * (m - 2)
    print(f"m={m} p={p} k={k} mode={mode}: ring dim {m**nvar}, predicted dim ideal = Q_1(m) = {Q}, quotient {m**nvar - Q}")
    t0 = time.time()
    gf = GF(p, 1)
    S = Span(gf, m ** nvar, batch=64)
    Js = matchings(N)
    assert len(Js) == 3
    for J in Js:
        f = psi(J, m, nvar) % p
        f = f.astype(np.uint8)
        k0 = J[0][1]
        if mode == 'all':
            rows = []
            for nu in itertools.product(range(m), repeat=nvar):
                g = f
                for i, e in enumerate(nu):
                    if e:
                        g = np.roll(g, e, axis=i)
                rows.append(g.reshape(-1))
                if len(rows) >= 512:
                    S.add(np.array(rows)); rows = []
            if rows:
                S.add(np.array(rows))
        else:
            # spanning set of Im(psi_J): t_{k0}^a t_{k1}^b psi_J, 0<=a,b<=m-2  (uses only t_j t_k phi = phi)
            (j1, k1) = J[1]
            rows = []
            for a in range(m - 1):
                ga = np.roll(f, a, axis=k0 - 1)
                for b in range(m - 1):
                    rows.append(np.roll(ga, b, axis=k1 - 1).reshape(-1))
            S.add(np.array(rows))
        print(f"  after J={J}: dim so far {S.dim()}  ({time.time()-t0:.1f}s)")
    d = S.dim()
    print(f"RESULT m={m} p={p}: dim (psi_J) F_p[G] = {d}; quotient dim = {m**nvar - d}; predicted {Q} / {m**nvar - Q}; "
          f"{'AGREES' if d == Q else 'DISAGREES'}  [{time.time()-t0:.1f}s]")

if __name__ == '__main__':
    main()
