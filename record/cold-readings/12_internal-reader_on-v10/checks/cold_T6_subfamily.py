# cold_T6: Remark 8.7(3), last sentence: q=3, k=2 (N=6), over F_3, 14 of the 15 matchings:
#   intersection count  dim F_3[x]/cap_{J in K}(I_J + (x_i^3))   (claimed 140)
#   sum count           dim F_3[x]/(E_K + (x_i^3)),  E_K = cap_{J in K} I_J   (claimed 141 = number of points)
import itertools, sys, numpy as np
from cold_lib import *

N, r, p = 6, 3, 3
Js = list(matchings(range(N)))

def poly_monos(nv, d):
    out = []
    def rec(i, left, cur):
        if i == nv - 1:
            out.append(tuple(cur + [left])); return
        for a in range(left + 1):
            rec(i + 1, left - a, cur + [a])
    rec(0, d, [])
    return out

def restr_matrix(K, d):
    src = poly_monos(N, d)
    tgt = poly_monos(N // 2, d); ti = {m: i for i, m in enumerate(tgt)}
    M = np.zeros((len(K) * len(tgt), len(src)), dtype=np.int64)
    boxcols = np.array([max(e) >= r for e in src])
    for jn, J in enumerate(K):
        for ci, e in enumerate(src):
            sign = 1; t = []
            for (a, b) in J:
                t.append(e[a] + e[b])
                if e[a] % 2: sign = -sign
            M[jn * len(tgt) + ti[tuple(t)], ci] = sign % p
    return M, boxcols

def sum_count(K):
    tot = 0
    for d in range(0, N * (r - 1) + 1):
        M, boxcols = restr_matrix(K, d)
        rk = rank_mod(M, p)
        rkb = rank_mod(M[:, boxcols], p) if boxcols.any() else 0
        tot += rk - rkb
    return tot

def inter_count(K):
    box = Box(N, r)
    DJ = [D_J(N, r, J) for J in K]
    return sum(span_rank_ideal(box, DJ, p).values())

def points(K):
    cnt = 0
    for x in itertools.product(range(3), repeat=N):
        if any(all((x[a] + x[b]) % 3 == 0 for (a, b) in J) for J in K):
            cnt += 1
    return cnt

print(f"full family (15): sum count = {sum_count(Js)}  intersection count = {inter_count(Js)}  points = {points(Js)}", flush=True)
for i in range(len(Js)):
    K = Js[:i] + Js[i + 1:]
    ic = inter_count(K)
    if i < 3:
        print(f"remove matching {i} {Js[i]}: sum count = {sum_count(K)}  intersection count = {ic}  points = {points(K)}", flush=True)
    else:
        print(f"remove matching {i} {Js[i]}: intersection count = {ic}  points = {points(K)}", flush=True)
print("FIN-OK")
