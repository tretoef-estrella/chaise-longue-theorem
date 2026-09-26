# regla269_p2.py — Grepy el Lector, 2026-09-24. Independent gate of INFORME_15 Theorem D, (Chain) and (P2):
# for mu <= mu~ (weak dominance, same parity, both with <= h parts) the option chains of length q-1 dominate position-wise.
import sys, itertools
def parts(n, maxp=None):
    if maxp is None: maxp = n
    if n == 0: yield (); return
    for p in range(min(n, maxp), 0, -1):
        for r in parts(n - p, p): yield (p,) + r
def S(l, t): return sum(l[:t])
def leq(a, b):
    L = max(len(a), len(b))
    return all(S(a, t) <= S(b, t) for t in range(1, L + 1))
def norm(l): return tuple(sorted([x for x in l if x > 0], reverse=True))
def options(mu, q):
    h = (q - 1) // 2; l = len(mu); out = []
    for j in range(l):
        m = list(mu); m[j] -= 1; out.append(norm(m))
    out += [norm(list(mu) + [1])] * (q - 1 - 2 * l)
    for j in range(l - 1, -1, -1):
        m = list(mu); m[j] += 1; out.append(norm(m))
    assert len(out) == q - 1
    return out
def run(q, M):
    h = (q - 1) // 2
    P = [p for n in range(M + 1) for p in parts(n) if len(p) <= h]
    chain_bad = 0; p2_bad = 0; pairs = 0
    for mu in P:
        o = options(mu, q)
        if any(not leq(o[i], o[i + 1]) for i in range(q - 2)): chain_bad += 1
    for a, b in itertools.product(P, P):
        if (sum(a) - sum(b)) % 2 or a == b or not leq(a, b): continue
        pairs += 1
        oa, ob = options(a, q), options(b, q)
        # only options with <= h parts are legal partitions; an illegal option is never in a down-set of Par
        for x, y in zip(oa, ob):
            if len(y) <= h and len(x) <= h and not leq(x, y): p2_bad += 1; print('P2 FAIL q=%d mu=%s mu~=%s %s vs %s' % (q, a, b, x, y)); break
            if len(y) <= h and len(x) > h: p2_bad += 1; print('P2 ILLEGAL q=%d mu=%s mu~=%s %s vs %s' % (q, a, b, x, y)); break
    print('q=%d |mu|<=%d partitions=%d chain_bad=%d pairs=%d P2_bad=%d' % (q, M, len(P), chain_bad, pairs, p2_bad), flush=True)
if __name__ == '__main__':
    for q, M in ((3, 30), (9, 14), (27, 12), (81, 11)): run(q, M)
