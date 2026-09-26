# b4.py — Fable, Mission 15: sealed bet B4. At (k,q) = (2,3): for EVERY nonempty subfamily K of the 15 matchings,
# compare dim (D_J : J in K)C  (C = F_3[y1..y5]/(y_i^2)) with |Gamma_K| (points of {+-1}^5 in some Gamma'_J, J in K).
import itertools, numpy as np, sys
sys.path.insert(0, '.')
from eng15 import matchings, rref
n = 5
Js = list(matchings(range(6)))
subsets = {d: [frozenset(S) for S in itertools.combinations(range(n), d)] for d in range(n+1)}
idx = {d: {S: i for i, S in enumerate(subsets[d])} for d in subsets}
def DJ(J):
    pairs = [(a-1, b-1) for (a, b) in J if a != 0]
    poly = {frozenset(): 1}
    for (a, b) in pairs:
        new = {}
        for S, c in poly.items():
            for v, sg in ((b, 1), (a, -1)):
                if v in S: continue
                T = S | {v}; new[T] = (new.get(T, 0) + c*sg) % 3
        poly = {S: c for S, c in new.items() if c}
    v = np.zeros(len(subsets[2]), dtype=np.int64)
    for S, c in poly.items(): v[idx[2][S]] = c
    return v
vecs = [DJ(J) for J in Js]
up = {}
for d in range(2, n):
    M = np.zeros((n, len(subsets[d]), len(subsets[d+1])), dtype=np.int64)
    for i in range(n):
        for S in subsets[d]:
            if i not in S: M[i, idx[d][S], idx[d+1][S | {i}]] = 1
    up[d] = M
def dimK(K):
    V, _ = rref(np.array([vecs[j] for j in K])); tot = V.shape[0]; d = 2
    while d < n and V.shape[0]:
        X = np.vstack([V @ up[d][i] for i in range(n)]) % 3
        V, _ = rref(X); tot += V.shape[0]; d += 1
    return tot
pts = list(itertools.product((1, -1), repeat=n))
def gammaJ(J):
    pairs = [(a-1, b-1) for (a, b) in J if a != 0]
    return sum(1 << p for p, y in enumerate(pts) if all(y[b] == -y[a] for (a, b) in pairs))
gm = [gammaJ(J) for J in Js]
worst = 0; nfail = 0; ex = None; tot = 0
for mask in range(1, 1 << 15):
    K = [j for j in range(15) if mask >> j & 1]
    g = 0
    for j in K: g |= gm[j]
    G = bin(g).count('1'); D = dimK(K); tot += 1
    assert D <= G, (K, D, G)
    if D < G:
        nfail += 1
        if ex is None or G - D > worst: worst = G - D; ex = (K, D, G)
print('B4 (2,3): subfamilies=%d  with dim < |Gamma_K|: %d  worst deficit=%d example=%s' % (tot, nfail, worst, ex))
