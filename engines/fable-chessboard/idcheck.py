# idcheck.py — Fable, Mission 15: exact check (in C = F_3[y_1..y_n]/(y^{q-1})) of the two identities of the rule lemmas.
#  L2/L2': f = sum_{b in S} eps_b * Delta(S\b) * D(y_1, y_b) has deg_{y1} <= q-1-r and [y1^{q-1-r}] f = +-Delta(S), |S| = r.
#  L3:     Delta({1} u B0) has deg_{y1} = |B0| and top coefficient +-Delta(B0).
import itertools, sys
def mul(a, b, r):
    out = {}
    for e, c in a.items():
        for f, d in b.items():
            g = tuple(x+y for x, y in zip(e, f))
            if max(g) < r: out[g] = (out.get(g, 0) + c*d) % 3
    return {e: c for e, c in out.items() if c}
def add(a, b, s=1):
    out = dict(a)
    for e, c in b.items(): out[e] = (out.get(e, 0) + s*c) % 3
    return {e: c for e, c in out.items() if c}
def mono(n, i, p=1): e = [0]*n; e[i] = p; return {tuple(e): 1}
def vdm(n, B, r):
    p = {tuple([0]*n): 1}
    for x, y in itertools.combinations(B, 2): p = mul(p, add(mono(n, x), mono(n, y), -1), r)
    return p
def D(n, a, b, q):
    return {tuple((s if i == a else (q-2-s if i == b else 0)) for i in range(n)): ((-1)**s) % 3 for s in range(q-1)}
def coeff(p, var, d): 
    out = {}
    for e, c in p.items():
        if e[var] == d: f = list(e); f[var] = 0; out[tuple(f)] = c
    return out
ok = True
for q in (9, 27):
    R = q-1
    for rr in range(1, 6):
        n = rr+1; S = list(range(1, n))
        f = {}
        for t, b in enumerate(S):
            eps = 1 if (len(S)-1-t) % 2 == 0 else -1     # cofactor sign along last row
            term = mul(vdm(n, [x for x in S if x != b], R), D(n, 0, b, q), R)
            f = add(f, term, eps)
        deg = max(e[0] for e in f) if f else -1
        top = coeff(f, 0, deg)
        V = vdm(n, S, R)
        good = deg == q-1-rr and (top == V or top == {e: (-c) % 3 for e, c in V.items()})
        ok &= good
        print('q=%d |S|=%d: deg_y1 f = %d (expected %d), top = +-Delta(S): %s' % (q, rr, deg, q-1-rr, good))
    for b0 in range(0, 5):
        n = b0+1; V = vdm(n, list(range(n)), R); deg = max(e[0] for e in V)
        top = coeff(V, 0, deg); V0 = vdm(n, list(range(1, n)), R)
        good = deg == b0 and (top == V0 or top == {e: (-c) % 3 for e, c in V0.items()})
        ok &= good
        print('q=%d L3 |B0|=%d: deg %d, top = +-Delta(B0): %s' % (q, b0, deg, good))
print('ALL IDENTITIES OK' if ok else 'SOME IDENTITY FAILED')
