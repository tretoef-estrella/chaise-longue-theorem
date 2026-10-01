# cold_T5: Theorem 7.1 of the note (fibre-rank statistic), the q=3 formula, the roots-of-unity identity,
#          and dim F[L]/K_(1)(L) = N_(1)(n)  (consequence of the propagation argument of Theorem 7.1).
import itertools, numpy as np, cmath
from collections import Counter
from cold_lib import *

def hilbert_series(r, N, p):
    box = Box(N, r)
    eodd = [elem_sym(N, j, r) for j in range(1, N + 1, 2)]
    E = span_rank_ideal(box, eodd, p)
    return [box.dim(d) - E[d] for d in range(box.top + 1)]

def steps_of(q):
    h = q // 2
    st = []
    for i in range(h):
        for s in (1, -1):
            e = [0] * h; e[i] = s; st.append(tuple(e))
    if q % 2 == 1:
        st.append(tuple([0] * h))
    return st

def walk_tables(q, n):
    h = q // 2; st = steps_of(q)
    T = [Counter({tuple([0] * h): 1})]
    for _ in range(n):
        nx = Counter()
        for pt, c in T[-1].items():
            for s in st:
                nx[tuple(a + b for a, b in zip(pt, s))] += c
        T.append(nx)
    return T

def stat_series(q, n, tiebreak):
    """sum over closed walks of t^stat, with stat from the note's definition; tiebreak = key function on steps."""
    h = q // 2; st = steps_of(q); T = walk_tables(q, n)
    # G[j][p] = polynomial (Counter exponent->count) of walks of length j from 0 to p
    G = [dict() for _ in range(n + 1)]
    G[0][tuple([0] * h)] = Counter({0: 1})
    for j in range(1, n + 1):
        for pt in T[j]:
            opts = []
            for c in st:
                prev = tuple(a - b for a, b in zip(pt, c))
                opts.append((T[j - 1].get(prev, 0), c, prev))
            opts.sort(key=lambda o: (-o[0], tiebreak(o[1])))
            poly = Counter()
            for rank, (cnt, c, prev) in enumerate(opts):
                if cnt == 0: continue
                for e, m in G[j - 1][prev].items():
                    poly[e + rank] += m
            G[j][pt] = poly
    P = G[n][tuple([0] * h)]
    top = max(P) if P else 0
    return [P.get(d, 0) for d in range(top + 1)]

def q3_formula(n):
    out = Counter()
    for w in itertools.product((-1, 0, 1), repeat=n):
        pos = 0; cnt = 0; ok = True
        for s in w:
            prev = pos; pos += s
            if pos == 0 and prev in (0, -1): cnt += 1
        if pos != 0: continue
        out[n - cnt] += 1
    top = max(out)
    return [out.get(d, 0) for d in range(top + 1)]

def strip(L):
    L = list(L)
    while L and L[-1] == 0: L.pop()
    return L

print("== Theorem 7.1: HS of F[L]/I_q(L) against sum over closed walks of t^stat (two tie-breaks)")
cells = [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (5, 2), (5, 3), (5, 4), (5, 5), (7, 2), (7, 3), (7, 4), (9, 3)]
HS = {}
for (q, n) in cells:
    for p in [3, 5, 1000003]:
        hs = strip(hilbert_series(q, n, p))
        HS[(q, n, p)] = hs
        s1 = strip(stat_series(q, n, lambda c: c))
        s2 = strip(stat_series(q, n, lambda c: tuple(-x for x in c)))
        print(f"  q={q} n={n} p={p}: HS={hs}  stat(tb1)==HS: {s1==hs}  stat(tb2)==HS: {s2==hs}", flush=True)
print("== q=3 closed formula stat = n - #{j : p_j = 0, p_{j-1} in {0,-1}}")
for n in range(2, 8):
    print(f"  n={n}: formula==HS(p=5): {strip(q3_formula(n))==HS[(3,n,5)]}", flush=True)
print("== roots of unity: sum_d w^d dim A_d = 1 for every (q-1)-th root of unity w != 1")
for (q, n) in cells:
    hs = HS[(q, n, 5)]
    cls = [0] * (q - 1)
    for d, a in enumerate(hs): cls[d % (q - 1)] += a
    ok = (cls[0] - 1 == cls[1]) and all(c == cls[1] for c in cls[1:])
    print(f"  q={q} n={n}: residue-class sums mod q-1 = {cls}  identity holds: {ok}", flush=True)

print("== K_(1)(L) = I_q(L) + (prod_{a in A} a^{q-1} prod_{x in P} x : |A|=|B|) : dim against N_(1)(n) = walks 0 -> eps_1")
for (q, n) in [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (5, 1), (5, 2), (5, 3), (5, 4), (7, 3)]:
    box = Box(n, q); h = q // 2
    gens = [elem_sym(n, j, q) for j in range(1, n + 1, 2)]
    for rr in range(0, n // 2 + 1):
        for A in itertools.combinations(range(n), rr):
            rest = [i for i in range(n) if i not in A]
            for P in itertools.combinations(rest, n - 2 * rr):
                e = [0] * n
                for a in A: e[a] = q - 1
                for x in P: e[x] += 1
                if max(e) < q:
                    gens.append({tuple(e): 1})
    w = walks_to(n, h, True, [1] + [0] * (h - 1))
    for p in [3, 5, 1000003]:
        dimK = sum(span_rank_ideal(box, gens, p).values())
        print(f"  q={q} n={n} p={p}: dim F[L]/K_(1) = {q**n-dimK}   N_(1)(n) = {w}   equal: {q**n-dimK==w}", flush=True)
print("FIN-OK")
