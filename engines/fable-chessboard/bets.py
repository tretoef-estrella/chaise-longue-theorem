# bets.py — Fable, Mission 15: scoring sealed bets B3 (q=3 annihilator) and B7 ((1,9) annihilator generators).
import sys, itertools, numpy as np
sys.path.insert(0, '.')
from eng15 import Basis, matchings, Q
def ideal_dim(n, r, gens):
    # gens: list of dicts exponent-tuple -> coeff (homogeneous or not; we split into homogeneous parts per generator)
    bydeg = {}
    for e in itertools.product(range(r), repeat=n): bydeg.setdefault(sum(e), []).append(e)
    idx = {e: i for d in bydeg for i, e in enumerate(bydeg[d])}
    G = {}
    for g in gens:
        for e, c in g.items():
            if max(e) < r and c % 3: G.setdefault(id(g), {}).setdefault(sum(e), {})[e] = c % 3
    hom = {}
    for parts in G.values():
        for d, p in parts.items(): hom.setdefault(d, []).append(p)
    tot = 0; V = None; dims = []
    for d in range(0, n*(r-1)+1):
        Bn = Basis(len(bydeg[d]))
        if V is not None and V.shape[0]:
            src = bydeg[d-1]
            for i in range(n):
                ok = []; to = []
                for j, e in enumerate(src):
                    if e[i]+1 < r:
                        f = list(e); f[i] += 1; ok.append(j); to.append(idx[tuple(f)])
                X = np.zeros((V.shape[0], len(bydeg[d])), dtype=np.int64); X[:, to] = V[:, ok]; Bn.add(X)
        if d in hom:
            X = np.zeros((len(hom[d]), len(bydeg[d])), dtype=np.int64)
            for i, p in enumerate(hom[d]):
                for e, c in p.items(): X[i, idx[e]] = c
            Bn.add(X)
        V = Bn.B; tot += V.shape[0]; dims.append(V.shape[0])
    return tot, dims
def polymul(p1, p2, r):
    out = {}
    for e, c in p1.items():
        for f, d in p2.items():
            g = tuple(a+b for a, b in zip(e, f))
            if max(g) < r: out[g] = (out.get(g, 0) + c*d) % 3
    return {e: c for e, c in out.items() if c}
def powsum(n, j, r):
    return {tuple(j if t == i else 0 for t in range(n)): 1 for i in range(n)} if j < r else {}
def ppow(p, e, n, r):
    out = {tuple([0]*n): 1}
    for _ in range(e): out = polymul(out, p, r)
    return out
mode = sys.argv[1]
if mode == 'B3':
    for k in range(1, 6):
        n = 2*k+1; r = 2
        gens = []
        for d in range(2, n+1):
            gens.append({tuple(1 if i in S else 0 for i in range(n)): 1 for S in itertools.combinations(range(n), d)})
        for S in itertools.combinations(range(n), k+2):
            gens.append({tuple(1 if i in S else 0 for i in range(n)): 1})
        tot, dims = ideal_dim(n, r, gens)
        target = 2**n - Q(k, 3)
        print('B3 k=%d dim((e_2..e_n)+m^{k+2}) = %d ; dim ann = 2^n - Q = %d  %s' % (k, tot, target, 'HIT' if tot == target else 'FALSIFIED'), flush=True)
if mode == 'B7':
    n, q = 3, 9; r = q-1
    p1 = powsum(n, 1, r)
    gens = [ppow(p1, q-1, n, r)]
    for j in range(3, 2*n+q, 2):
        pj = powsum(n, j, r); p1j = ppow(p1, j, n, r)
        g = dict(pj)
        for e, c in p1j.items(): g[e] = (g.get(e, 0) - c) % 3
        gens.append({e: c for e, c in g.items() if c})
    tot, dims = ideal_dim(n, r, gens)
    target = r**n - Q(1, q)
    print('B7 (1,9): dim(E\' + p_1^{q-1}) = %d ; dim ann = %d ; %s' % (tot, target, 'extra generators needed (B7 HIT)' if tot < target else 'generated (B7 FALSIFIED)'), dims)
