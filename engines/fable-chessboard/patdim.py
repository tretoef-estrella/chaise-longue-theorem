# patdim.py — Fable, Mission 15. Usage: python3 -u patdim.py M Q 'P'   (P = python list of types, e.g. "[(1,(3,)),(2,())]")
# dim of the pattern ideal V(m;P) in C_m = F_3[y]/(y^{q-1}) (graded closure, mod-3 RREF) versus |Z(m;P)| (brute force on
# (F_q^x)^m, witness by exhaustive search over index sets — independent of the Gale-Ryser code of peel*.py).
import sys, itertools, numpy as np
sys.path.insert(0, '.')
from eng15 import Basis
m, q, P = int(sys.argv[1]), int(sys.argv[2]), eval(sys.argv[3])
r = q-1; h = r//2
Dab = [((-1)**s) % 3 for s in range(q-1)]
def mul(p1, p2):
    out = {}
    for e, c in p1.items():
        for f, d in p2.items():
            g = tuple(a+b for a, b in zip(e, f))
            if max(g) >= r: continue
            out[g] = (out.get(g, 0) + c*d) % 3
    return {e: c for e, c in out.items() if c}
def var(i, p=1):
    e = [0]*m; e[i] = p; return {tuple(e): 1}
def D(a, b):
    out = {}
    for s in range(q-1):
        e = [0]*m; e[a] += s; e[b] += q-2-s; out[tuple(e)] = Dab[s]
    return out
def Vdm(B):
    p = {tuple([0]*m): 1}
    for x, y in itertools.combinations(B, 2):
        p = mul(p, {**var(x), **{k: (-v) % 3 for k, v in var(y).items()}})
    return p
def placements(s, beta):
    idx = list(range(m))
    def rec_pairs(avail, k):
        if k == 0: yield [], avail; return
        if len(avail) < 2*k: return
        a = avail[0]
        for j in range(1, len(avail)):
            rest = avail[1:j] + avail[j+1:]
            for ps, left in rec_pairs(rest, k-1): yield [(a, avail[j])] + ps, left
        for ps, left in rec_pairs(avail[1:], k): yield ps, [a] + left   # a unused (kept for blocks)
    def rec_blocks(avail, bl):
        if not bl: yield []; return
        for B in itertools.combinations(avail, bl[0]):
            rest = [x for x in avail if x not in B]
            for more in rec_blocks(rest, bl[1:]): yield [B] + more
    seen = set()
    for ps, left in rec_pairs(idx, s):
        for bls in rec_blocks(left, list(beta)):
            key = (frozenset(frozenset(p) for p in ps), frozenset(frozenset(b) for b in bls))
            if key in seen: continue
            seen.add(key); yield ps, bls
gens = {}
for (s, beta) in P:
    for ps, bls in placements(s, beta):
        p = {tuple([0]*m): 1}
        for (a, b) in ps: p = mul(p, D(a, b))
        for B in bls: p = mul(p, Vdm(B))
        if p:
            d = sum(next(iter(p)))
            gens.setdefault(d, []).append(p)
bydeg = {}
for e in itertools.product(range(r), repeat=m): bydeg.setdefault(sum(e), []).append(e)
idx = {}
for d in bydeg:
    for i, e in enumerate(bydeg[d]): idx[e] = i
tot = 0; V = None; d0 = min(gens)
for d in range(d0, m*(r-1)+1):
    Bn = Basis(len(bydeg[d]))
    if V is not None and V.shape[0]:
        src = bydeg[d-1]
        for i in range(m):
            ok = []; to = []
            for j, e in enumerate(src):
                if e[i]+1 < r:
                    f = list(e); f[i] += 1; ok.append(j); to.append(idx[tuple(f)])
            X = np.zeros((V.shape[0], len(bydeg[d])), dtype=np.int64); X[:, to] = V[:, ok]; Bn.add(X)
    if d in gens:
        X = np.zeros((len(gens[d]), len(bydeg[d])), dtype=np.int64)
        for i, p in enumerate(gens[d]):
            for e, c in p.items(): X[i, idx[e]] = c
        Bn.add(X)
    V = Bn.B; tot += V.shape[0]
# brute-force |Z|
def neg(v): return (v + h) % r
def has(M, s, beta):
    n_ = len(M)
    def rec_p(avail, k):
        if k == 0: yield avail; return
        if len(avail) < 2*k: return
        a = avail[0]
        for j in range(1, len(avail)):
            if M[avail[j]] == neg(M[a]):
                yield from rec_p(avail[1:j] + avail[j+1:], k-1)
        for left in rec_p(avail[1:], k): yield [a] + left
    def blocks(avail, bl):
        if not bl: return True
        for B in itertools.combinations(avail, bl[0]):
            if len(set(M[x] for x in B)) == len(B):
                if blocks([x for x in avail if x not in B], bl[1:]): return True
        return False
    for left in rec_p(list(range(n_)), s):
        if blocks(left, list(beta)): return True
    return False
Z = sum(1 for M in itertools.product(range(r), repeat=m) if any(has(M, s, beta) for (s, beta) in P))
print('PATDIM m=%d q=%d P=%s dim V=%d |Z|=%d %s' % (m, q, P, tot, Z, 'EQUAL' if tot == Z else ('dim>=|Z|' if tot > Z else 'DIM < |Z| !!')), flush=True)
