# cold_T2: Corollary 8.6(i), the map theta : M -> C, f -> coefficient of x_0^{r-1}.
# checks: f determined by f_{r-1} (injectivity of theta on M), theta(M) = (D_J : J)C, dim = Q_k(q).
import itertools, numpy as np
from cold_lib import *

def run(r, N, p):
    allm = list(itertools.product(range(r), repeat=N))
    gi = {m: i for i, m in enumerate(allm)}
    ym = list(itertools.product(range(r), repeat=N - 1))
    yi = {m: i for i, m in enumerate(ym)}
    Js = list(matchings(range(N)))
    rows = []
    for J in Js:
        f = D_J(N, r, J)
        for m in allm:
            h = pmul(f, {m: 1}, r)
            if h:
                v = np.zeros(len(allm), dtype=np.int64)
                for e, c in h.items(): v[gi[e]] = c % p
                rows.append(v)
    B, piv = rref_mod(np.array(rows), p)          # basis of M
    dimM = B.shape[0]
    # theta
    T = np.zeros((dimM, len(ym)), dtype=np.int64)
    for e, i in gi.items():
        if e[0] == r - 1:
            T[:, yi[e[1:]]] = B[:, i]
    rk_theta = rank_mod(T, p)
    # recursion f_{u-1} = -sigma f_u : check on the basis of M
    rec_ok = True
    sigma = {}
    for i in range(N - 1):
        e = [0] * (N - 1); e[i] = 1; sigma[tuple(e)] = 1
    for row in B:
        comps = []
        for u in range(r):
            fu = {}
            for e, i in gi.items():
                if e[0] == u and row[i] % p:
                    fu[e[1:]] = int(row[i])
            comps.append(fu)
        for u in range(1, r):
            lhs = comps[u - 1]
            rhs = pmul(sigma, comps[u], r)
            diff = padd(lhs, rhs, 1)       # f_{u-1} + sigma f_u  must be 0 mod p
            if any(c % p for c in diff.values()):
                rec_ok = False
    # the ideal (D_J : J) C in the y-ring (pairs not containing 0), variables y_1..y_{N-1} = indices 0..N-2
    rowsC = []
    for J in Js:
        f = one(N - 1)
        for (a, b) in J:
            if a == 0: continue
            f = pmul(f, D_r(N - 1, r, a - 1, b - 1), r)
        for m in ym:
            h = pmul(f, {m: 1}, r)
            if h:
                v = np.zeros(len(ym), dtype=np.int64)
                for e, c in h.items(): v[yi[e]] = c % p
                rowsC.append(v)
    rowsC = np.array(rowsC)
    rkC = rank_mod(rowsC, p)
    rkU = rank_mod(np.vstack([rowsC, T]), p)
    return dimM, rk_theta, rec_ok, rkC, rkU

for (r, N) in [(2, 2), (2, 4), (2, 6), (4, 2), (4, 4), (6, 4)]:
    q = r + 1; k = N // 2 - 1
    Q = closed_walks(N, r // 2, False)
    for p in [2, 3, 5, 1000003]:
        dimM, rk_theta, rec_ok, rkC, rkU = run(r, N, p)
        print(f"q={q} k={k} (r={r},N={N}) p={p}: dim M={dimM}  rank theta(M)={rk_theta}  recursion f_(u-1)=-sigma f_u: {rec_ok}  "
              f"dim (D_J)C={rkC}  dim(theta(M)+(D_J)C)={rkU}  Q_k(q)={Q}  ALL-EQUAL: {dimM==rk_theta==rkC==rkU==Q}", flush=True)
print("FIN-OK")
