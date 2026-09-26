"""
bip_roots_char0_proxy.py — Remark 7.9(2): dimensions of the bipartite root ideals in characteristic 0 (proxy: exact rank
modulo two large primes 10007, 10009; rank_Q >= rank_{F_p} always, with equality for all but finitely many p) versus the
paper's claims dim_Q I^bal_a = 4, 24, 169 (a=1,2,3; q=3), dim_Q I^ph_a = 18, 126 (a=1,2; q=3), dim_Q I^bal_2 = 129, 416, 1025
(q=5,7,9). Also the mod-3 / mod-5 / mod-7 values (= N_bal, N_ph by Corollary 7.8) for comparison. Referee's own code.
"""
import sys, itertools, numpy as np
sys.path.insert(0, 'scripts')
from gf_linalg import GF, Span

def gens_bal(a, q):
    """generators prod_i (x_i - z_{sigma(i)})^{q-1} in R_{[a],[a]}, as dense arrays over Z (exponents < q)"""
    nv = 2 * a
    def var_shift(f, v):  # multiply by variable v (0..nv-1), truncated
        g = np.zeros_like(f); src = [slice(None)] * nv; dst = [slice(None)] * nv
        src[v] = slice(0, q - 1); dst[v] = slice(1, q); g[tuple(dst)] = f[tuple(src)]; return g
    out = []
    for sigma in itertools.permutations(range(a)):
        f = np.zeros((q,) * nv, dtype=np.int64); f[(0,) * nv] = 1
        for i in range(a):
            for _ in range(q - 1):
                f = var_shift(f, i) - var_shift(f, a + sigma[i])
        out.append(f)
    return out, nv

def gens_ph(a, q):
    nv = 2 * a + 1
    def var_shift(f, v):
        g = np.zeros_like(f); src = [slice(None)] * nv; dst = [slice(None)] * nv
        src[v] = slice(0, q - 1); dst[v] = slice(1, q); g[tuple(dst)] = f[tuple(src)]; return g
    out = []
    for i0 in range(a + 1):
        others = [i for i in range(a + 1) if i != i0]
        for sigma in itertools.permutations(range(a)):
            f = np.zeros((q,) * nv, dtype=np.int64); f[(0,) * nv] = 1
            for idx, i in enumerate(others):
                for _ in range(q - 1):
                    f = var_shift(f, i) - var_shift(f, a + 1 + sigma[idx])
            out.append(f)
    return out, nv

def ideal_dim(gens, nv, q, p):
    gf = GF(p, 1); S = Span(gf, q ** nv, batch=256)
    frontier = S.add(np.array([g.reshape(-1) % p for g in gens]).astype(gf.dtype))
    while frontier.shape[0]:
        F = frontier.reshape((-1,) + (q,) * nv); new = []
        for v in range(nv):
            g = np.zeros_like(F); src = [slice(None)] * (nv + 1); dst = [slice(None)] * (nv + 1)
            src[v + 1] = slice(0, q - 1); dst[v + 1] = slice(1, q); g[tuple(dst)] = F[tuple(src)]
            new.append(g.reshape(F.shape[0], -1))
        new = np.vstack(new); new = new[new.any(axis=1)]
        frontier = S.add(new) if new.shape[0] else new[:0]
    return S.dim()

cases = [('bal', 1, 3, 4), ('bal', 2, 3, 24), ('bal', 3, 3, 169), ('ph', 1, 3, 18), ('ph', 2, 3, 126), ('bal', 2, 5, 129), ('bal', 2, 7, 416), ('bal', 2, 9, 1025)]
print("prediction (paper, Remark 7.9(2) / §12.4): the char-0 values listed; mod p (p | q) the values N_bal/N_ph")
for kind, a, q, claim in cases:
    gens, nv = gens_bal(a, q) if kind == 'bal' else gens_ph(a, q)
    p0 = 3 if q % 3 == 0 else (5 if q % 5 == 0 else 7)
    d0 = ideal_dim(gens, nv, q, p0)
    d1 = ideal_dim(gens, nv, q, 10007); d2 = ideal_dim(gens, nv, q, 10009)
    print(f"I^{kind}_{a} at q={q}: dim mod {p0} = {d0}; dim mod 10007 = {d1}; mod 10009 = {d2}; paper's char-0 claim {claim}: {'AGREES' if d1 == d2 == claim else 'DISAGREES'}", flush=True)
