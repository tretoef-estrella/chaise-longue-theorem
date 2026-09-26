# peel.py — Fable, Mission 15. Usage: python3 -u peel.py K Q
# Checks the combinatorial KEY LEMMA of the peeling induction (INFORME_15, STEP 3) on the whole tree below the root
# (m, P) = (2k+1, {(k, ())}), for one q.  A "type" (s, beta): s disjoint pairs {a,b} with y_b = -y_a, plus disjoint
# blocks of sizes beta (each >= 2) with pairwise distinct values inside each block.  Z(m;P) = points of (F_q^x)^m having
# a witness of some type in P.  Peeling y_1: fibre F(M') = {y_1 : M'+y_1 in Z}.  Child rules (slice W_{q-2-i}):
#   L1: (s,beta) itself;  L3: (s, beta with one block b -> b-1) if b-1 <= q-2-i;  L2: (s-1, beta + {i+1}) if s >= 1;
#   L2': (s-1, beta with one block i -> i+1) if s >= 1.
# KEY: every M' with |F(M')| > i lies in Z(m-1; P_i).  Also reports whether equality holds, and sum_i |pi_{>i}| = |Z|.
import sys, itertools
from math import factorial
from collections import Counter
k, q = int(sys.argv[1]), int(sys.argv[2]); h = (q-1)//2; NV = q-1
def feasible(m, t): return 2*t[0] + sum(t[1]) <= m
def canon(m, P): return frozenset(t for t in P if feasible(m, t))
def gr_ok(r, beta):
    for l in range(1, len(beta)+1):
        if sum(beta[:l]) > sum(min(x, l) for x in r): return False
    return True
def witness(cnt, s, beta):
    caps = [min(cnt[u], cnt[u+h]) for u in range(h)]
    def rec(u, left, r):
        if left == 0: return gr_ok(r, beta)
        if u == h: return False
        for p in range(min(caps[u], left), -1, -1):
            r2 = r
            if p:
                r2 = list(r); r2[u] -= p; r2[u+h] -= p
            if rec(u+1, left-p, r2): return True
        return False
    return rec(0, s, list(cnt))
memo_in = {}
def inZ(ms, P):
    key = (ms, P)
    if key in memo_in: return memo_in[key]
    cnt = [0]*NV
    for v in ms: cnt[v] += 1
    res = any(witness(cnt, s, beta) for (s, beta) in P)
    memo_in[key] = res; return res
def mult(ms):
    c = Counter(ms); r = factorial(len(ms))
    for x in c.values(): r //= factorial(x)
    return r
def children(m, P, i):
    out = set()
    for (s, beta) in P:
        out.add((s, beta))
        for j, b in enumerate(beta):
            if b-1 <= q-2-i:
                nb = list(beta[:j]) + list(beta[j+1:]) + ([b-1] if b-1 >= 2 else [])
                out.add((s, tuple(sorted(nb, reverse=True))))
        if s >= 1:
            nb = list(beta) + ([i+1] if i+1 >= 2 else [])
            out.add((s-1, tuple(sorted(nb, reverse=True))))
            for j, b in enumerate(beta):          # L2': the cofactor block S\b is a block of size i of the generator
                if b == i:
                    nb = list(beta[:j]) + list(beta[j+1:]) + [i+1]
                    out.add((s-1, tuple(sorted(nb, reverse=True))))
    return canon(m-1, out)
seen = {}; bad = []; nodes = 0; strict = 0
def check(m, P):
    global nodes, strict
    if (m, P) in seen: return seen[(m, P)]
    nodes += 1
    if m == 0:
        z = 1 if (0, ()) in P else 0; seen[(m, P)] = z; return z
    Zsize = sum(mult(ms) for ms in itertools.combinations_with_replacement(range(NV), m) if inZ(ms, P))
    fib = {}
    for ms in itertools.combinations_with_replacement(range(NV), m-1):
        fib[ms] = sum(1 for v in range(NV) if inZ(tuple(sorted(ms + (v,))), P))
    tot = 0
    Pall = {}
    for i in range(q-2, -1, -1):          # monotonicity: W_j is contained in W_{j+1}, so P_i inherits P_{i'} for i' > i
        Pall[i] = canon(m-1, set(children(m, P, i)) | (set(Pall[i+1]) if i+1 in Pall else set()))
    for i in range(q-1):
        A = [ms for ms in fib if fib[ms] > i]
        Pi = Pall[i]
        B = [ms for ms in fib if inZ(ms, Pi)]
        Aset = set(A); Bset = set(B)
        if not Aset <= Bset: bad.append((m, sorted(P), i, sorted(Pi), len(Aset - Bset)))
        if Bset != Aset: strict += 1
        tot += sum(mult(ms) for ms in A)
        if Pi and Aset: check(m-1, Pi)
    assert tot == Zsize, (m, P, tot, Zsize)
    seen[(m, P)] = Zsize; return Zsize
root = canon(2*k+1, {(k, ())})
z = check(2*k+1, root)
if len(sys.argv) > 3:
    for (m, P) in sorted(seen, key=lambda x: -x[0]): print('  node m=%d |Z|=%d P=%s' % (m, seen[(m, P)], sorted(P)))
print('PEEL k=%d q=%d |Gamma\'|=%d nodes=%d KEY-failures=%d strict-inclusions=%d' % (k, q, z, nodes, len(bad), strict), flush=True)
for b in bad[:15]: print('  FAIL m=%d P=%s i=%d P_i=%s missing=%d' % b)
