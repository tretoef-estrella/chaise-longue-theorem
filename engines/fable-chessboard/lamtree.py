# lamtree.py — Fable, Mission 15. The peeling tree of Gamma' in terms of the multiplicity partition lambda of the
# unpaired residue R(M).  Node = (m, Lambda), Lambda a set of partitions (|lam| <= m, |lam| = m mod 2, len <= h).
# fibre(lam') = #{parts j: lam'-e_j in Lambda} + #{parts j: lam'+e_j in Lambda} + (q-1-2 len(lam'))[lam' u (1) in Lambda].
import sys
k, q = int(sys.argv[1]), int(sys.argv[2]); h = (q-1)//2
def parts_upto(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for p in range(min(n, mx), 0, -1):
        for r in parts_upto(n-p, p): yield (p,) + r
def allpar(m): return [l for s in range(m % 2, m+1, 2) for l in parts_upto(s) if len(l) <= h]
def srt(l): return tuple(sorted([x for x in l if x > 0], reverse=True))
def fibre(l, L):
    f = 0
    for j in range(len(l)):
        a = list(l); a[j] -= 1
        if srt(a) in L: f += 1
        b = list(l); b[j] += 1
        if srt(b) in L: f += 1
    if len(l) < h and srt(l + (1,)) in L: f += q-1-2*len(l)
    return f
nodes = {}
def run(m, L):
    if (m, L) in nodes or m == 0: return
    fib = {l: fibre(l, L) for l in allpar(m-1)}
    ch = []
    vals = sorted(set(fib.values()))
    prev = None
    for i in range(q-1):
        Li = frozenset(l for l in fib if fib[l] > i)
        if Li != prev and Li: ch.append((i, Li)); prev = Li
    nodes[(m, L)] = ch
    for i, Li in ch: run(m-1, Li)
root = (2*k+1, frozenset([(1,)]))
run(*root)
print('k=%d q=%d nodes=%d' % (k, q, len(nodes)))
if len(sys.argv) > 3:
    for (m, L) in sorted(nodes, key=lambda x: (-x[0], len(x[1]))):
        print('m=%d Lambda=%s' % (m, sorted(L, key=lambda l: (sum(l), l))))
# --- check: every node Lambda is a down-set for weak dominance (partial sums of largest parts), within its parity
def wdom(a, b):   # a <= b in weak dominance
    sa = sb = 0
    for j in range(max(len(a), len(b))):
        sa += a[j] if j < len(a) else 0; sb += b[j] if j < len(b) else 0
        if sa > sb: return False
    return True
bad = 0
for (m, L), ch in nodes.items():
    for (i, Li) in ch:
        P = allpar(m-1)
        for mu in Li:
            for la in P:
                if wdom(la, mu) and la not in Li: bad += 1
for (m, L) in nodes:
    for mu in L:
        for la in allpar(m):
            if wdom(la, mu) and la not in L: bad += 1
print('down-set violations:', bad)
