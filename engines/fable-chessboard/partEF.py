# (i) Lemma V gate: z^2 G_r(n) - (z - a) G_r(n+1) == 0 mod box, exact, in n+1 variables.
# (ii) ranks of W_{r-1,r}(v) over Q vs F_3.
import itertools
from fractions import Fraction
def Gr(r, n, V, q):   # G_r(A;B) in the first n of V variables; A = 0..r-1, B = r..2r-1
    A = list(range(r)); B = list(range(r, 2*r)); rest = [i for i in range(n) if i not in B]
    out = {}
    for S in itertools.combinations(rest, n-r-1):
        t = [0]*V
        for i in A: t[i] = q-2
        for i in S: t[i] += 1
        out[tuple(t)] = 1
    return out
def mulm(p, e, c=1, q=None):
    out = {}
    for k, v in p.items():
        t = tuple(a+b for a, b in zip(k, e))
        if max(t) >= q: continue
        out[t] = (out.get(t, 0)+c*v) % 3
    return out
bad = 0
for q in (9, 27, 81):
    for r in (1, 2, 3):
        for n in range(2*r, 2*r+4):
            V = n+1; z = n
            ez2 = [0]*V; ez2[z] = 2; ez = [0]*V; ez[z] = 1; ea = [0]*V; ea[0] = 1
            lhs = mulm(Gr(r, n, V, q), ez2, 1, q)
            g1 = {}
            Ab = Gr(r, n+1, V, q)
            for k, v in mulm(Ab, ez, 1, q).items(): g1[k] = (g1.get(k, 0)+v) % 3
            for k, v in mulm(Ab, ea, -1, q).items(): g1[k] = (g1.get(k, 0)+v) % 3
            d = {k: (lhs.get(k, 0)-g1.get(k, 0)) % 3 for k in set(lhs) | set(g1)}
            ok = all(v == 0 for v in d.values())
            if not ok: bad += 1
print("Lemma V (z^2 G_r(n) == (z-a) G_r(n+1) mod box): cells q=9,27,81, r=1..3, n=2r..2r+3:", 36, "failed:", bad)
def rank(rows, p):
    M = [[Fraction(x) for x in r] for r in rows] if p == 0 else [[x % p for x in r] for r in rows]
    rk = 0; nc = len(M[0]) if M else 0
    for c in range(nc):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        pv = M[rk][c]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c]/pv if p == 0 else (M[i][c]*pow(int(pv), p-2, p)) % p
                M[i] = [(a-f*b) if p == 0 else (a-f*b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk
for r in range(2, 6):
    line = []
    for v in range(r, 2*r+1):
        Bs = list(itertools.combinations(range(v), r)); Es = list(itertools.combinations(range(v), r-1))
        rows = [[1 if set(e) <= set(b) else 0 for b in Bs] for e in Es]
        rq, r3 = rank(rows, 0), rank(rows, 3)
        line.append("v=%d(n=%d): Q %d, F3 %d / %d" % (v, v+r+1, rq, r3, len(Bs)))
    print("r=%d: " % r + "; ".join(line))
