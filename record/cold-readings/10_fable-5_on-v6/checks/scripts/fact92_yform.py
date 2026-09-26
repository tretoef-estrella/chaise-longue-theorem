"""
fact92_yform.py — reproduce Fact 9.2 of the paper (a computed, unused statement) with the referee's own code:
  at q = 9, k = 2, in C = F_3[y_1..y_5]/(y_i^8),  D(a,b) = Σ_{u=0}^{q-2} (-1)^u a^u b^{q-2-u},  D_J = Π_{pairs of J avoiding 0} D(y_j, y_k):
  dim (D_J : J ∈ 𝒥) C  should be Q_2(9) = 5120 (Theorem B),
  and for K = 𝒥 ∖ {[[0,1],[2,3],[4,5]], [[0,2],[1,5],[3,4]]}:  dim (D_J : J ∈ K) C = 4730 < 4736 = |Γ_K|  (Fact 9.2).
|Γ_K| is enumerated directly from [DS, Definition 1.3] in μ_9^5.
usage: python3 fact92_yform.py
"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gf_linalg import GF, Span

q = 9; p = 3; k = 2; nvar = 5; box = q - 1  # exponents 0..7
N = 2 * k + 2

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

def poly_mul(f, g):
    """truncated product in C: arrays of shape (box,)*nvar over Z, exponents >= box dropped"""
    out = np.zeros_like(f)
    nz = np.argwhere(g)
    for idx in nz:
        c = g[tuple(idx)]
        sl_src = tuple(slice(0, box - e) for e in idx)
        sl_dst = tuple(slice(e, box) for e in idx)
        out[sl_dst] += c * f[sl_src]
    return out % p

def D_pair(a, b):
    """D(y_a, y_b) as an array (variables 1..5 -> axes 0..4)"""
    f = np.zeros((box,) * nvar, dtype=np.int64)
    for u in range(q - 1):
        e = [0] * nvar; e[a - 1] += u; e[b - 1] += q - 2 - u
        if max(e) < box:
            f[tuple(e)] += (-1) ** u
    return f % p

def D_J(J):
    f = np.zeros((box,) * nvar, dtype=np.int64); f[(0,) * nvar] = 1
    for (a, b) in J:
        if a == 0:
            continue
        f = poly_mul(f, D_pair(a, b))
    return f

def ideal_dim(gens):
    gf = GF(p, 1)
    S = Span(gf, box ** nvar, batch=256)
    frontier = S.add(np.array([g.reshape(-1) % p for g in gens], dtype=np.uint8))
    while frontier.shape[0]:
        F = frontier.reshape((-1,) + (box,) * nvar)
        new = []
        for i in range(nvar):
            sh = np.zeros_like(F)
            src = [slice(None)] * (nvar + 1); dst = [slice(None)] * (nvar + 1)
            src[i + 1] = slice(0, box - 1); dst[i + 1] = slice(1, box)
            sh[tuple(dst)] = F[tuple(src)]
            new.append(sh.reshape(F.shape[0], -1))
        new = np.vstack(new); new = new[new.any(axis=1)]
        frontier = S.add(new) if new.shape[0] else new[:0]
    return S.dim()

def gamma_K(K, m):
    tot = 0
    pairs = [[(a, b) for (a, b) in J if a != 0] for J in K]
    for a in itertools.product(range(1, m), repeat=nvar):
        for P in pairs:
            if all((a[i - 1] + a[j - 1]) % m == 0 for (i, j) in P):
                tot += 1; break
    return tot

if __name__ == '__main__':
    t0 = time.time()
    Js = matchings(N)
    assert len(Js) == 15
    excl = [[(0, 1), (2, 3), (4, 5)], [(0, 2), (1, 5), (3, 4)]]
    K = [J for J in Js if J not in excl]
    assert len(K) == 13
    print("prediction: full family 5120 (= Q_2(9)); K: 4730 < |Γ_K| = 4736")
    gK = gamma_K(K, q); print(f"|Γ_K| (enumerated) = {gK}   [{time.time()-t0:.1f}s]", flush=True)
    dK = ideal_dim([D_J(J) for J in K]); print(f"dim (D_J : J ∈ K) C = {dK}   [{time.time()-t0:.1f}s]", flush=True)
    dF = ideal_dim([D_J(J) for J in Js]); print(f"dim (D_J : J ∈ 𝒥) C = {dF}   [{time.time()-t0:.1f}s]", flush=True)
    print(f"RESULT: full {dF} (paper 5120), K {dK} (paper 4730), |Γ_K| {gK} (paper 4736): "
          f"{'AGREES' if (dF, dK, gK) == (5120, 4730, 4736) else 'DISAGREES'}")
