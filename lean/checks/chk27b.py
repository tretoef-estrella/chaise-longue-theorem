# Piece 27, exact form sent: per colouring c (colours on 1..d, c_0 forced), the closed tuples of the
# model T_m = (Z/q x Z/r) minus (0,0), neg = negation, of length N = 2k+2 with colour cExt c number
# [compatible] * N1 * prod_zeta Nzeta, N1 := #closed tuples in (Z/q minus 0)^{|C_1|} (index 0 NOT special).
import itertools
from collections import Counter
exec(open('chk27.py').read().split('cells = ')[0])   # reuse closed, Nbal, Nph, gamma
def closed_count(L, q):
    return sum(1 for w in itertools.product(range(1,q), repeat=L) if closed(w, q))
def run(m, n, q, r, neg=False):
    N = n + 2
    # per-colour tally of closed tuples of T_m (brute), via the gamma enumeration g_1..g_{n+1}, g_0 forced
    tally = Counter()
    for g in itertools.product(range(1, m), repeat=n+1):
        g0 = (-sum(g)) % m
        if g0 == 0: continue
        full = (g0,) + g
        if closed(full, m):
            tally[tuple(x % r for x in g)] += 1
    fails = 0; tot = 0
    for c in itertools.product(range(r), repeat=n+1):
        ext = ((-sum(c)) % r,) + c
        cls = {}
        for i, z in enumerate(ext): cls.setdefault(z, []).append(i)
        comp = len(cls.get(0, [])) % 2 == 0 and all(len(cls.get(z, [])) == len(cls.get((-z) % r, [])) for z in range(1, r))
        val = 0
        if comp:
            L1 = len(cls.get(0, []))
            val = closed_count(L1 - 1 if (neg and 0 in cls.get(0, [])) else L1, q)
            for z in range(1, r):
                if z > (-z) % r: continue
                A, B = cls.get(z, []), cls.get((-z) % r, [])
                al = len([i for i in A if i]); be = len([i for i in B if i])
                val *= Nph(min(al, be), q) if (0 in A or 0 in B) else Nbal(al, q)
        tot += val
        if val != tally.get(c, 0): fails += 1
    return tot, fails
checks = 0; bad = 0; negfire = 0
for (m, n) in [(15,2),(21,2),(45,2),(15,4)]:
    for q in [d for d in (3,5,7,9) if m % d == 0 and (m//d) % 3 != 0 or d in (3,) and m % 9 != 0]:
        pass
    ps = sorted({d for d in range(2, m+1) if m % d == 0 and all(d % e for e in range(2, d))})
    for p in ps:
        q = 1
        while m % (q*p) == 0: q *= p
        r = m // q
        tot, f = run(m, n, q, r)
        totn, fn = run(m, n, q, r, neg=True)
        checks += 1; bad += (f > 0); negfire += (fn > 0)
        print(f"m={m} n={n} q={q} r={r}: sum={tot} per-colouring mismatches={f} | control: sum={totn} mismatches={fn}", flush=True)
print(f"cells {checks}, cells with a mismatch {bad}, control fired {negfire}/{checks}")
