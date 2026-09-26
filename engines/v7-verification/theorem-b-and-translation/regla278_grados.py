# regla278b — gate: graded ranks of C/(D_J)C (root down-set {(1)}) are the same in every characteristic.
# Prediction (rank argument, degree by degree): identical graded vectors for p = 2, 3, 5, 7, 10007. ESTIMATE: m<=5, q=5: 4^5=1024 monomials, < 50 MB, < 2 min.
import sys, itertools; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))  # repo copy
import numpy as np
from regla276_igualdad import tight_patterns, poly_mul
def graded(q, p, m):
    e = q - 2; mons = list(itertools.product(range(q - 1), repeat=m)); mi = {x: i for i, x in enumerate(mons)}
    def var(i, d): t = [0] * m; t[i] = d; return tuple(t)
    def Dp(a, b): return {tuple(x + y for x, y in zip(var(a, u), var(b, q - 2 - u))): (-1) ** u for u in range(q - 1)}
    basis = {}
    def add(v):
        v = v % p
        for c in sorted(basis):
            if v[c]: v = (v - v[c] * basis[c]) % p
        nz = np.nonzero(v)[0]
        if len(nz) == 0: return False
        c = int(nz[0]); v = (v * pow(int(v[c]), p - 2, p)) % p
        for c2 in list(basis):
            if basis[c2][c]: basis[c2] = (basis[c2] - basis[c2][c] * v) % p
        basis[c] = v; return True
    for P, B in tight_patterns(list(range(m)), (1,)):
        f = {tuple([0] * m): 1}
        for a, b in P: f = poly_mul(f, Dp(a, b), e)
        v = np.zeros(len(mons), dtype=np.int64)
        for k2, c in f.items(): v[mi[k2]] = (v[mi[k2]] + c) % p
        add(v)
    grew = True
    while grew:
        grew = False
        for r in list(basis.values()):
            for i in range(m):
                w = np.zeros(len(mons), dtype=np.int64)
                for j in np.nonzero(r)[0]:
                    t = list(mons[j]); t[i] += 1
                    if t[i] <= e: w[mi[tuple(t)]] = (w[mi[tuple(t)]] + r[j]) % p
                if w.any() and add(w): grew = True
    deg = [0] * (m * e + 1)
    for c in basis: deg[sum(mons[c])] += 1
    return deg
for q, m in ((5, 3), (7, 3), (5, 5)):
    rows = {p: graded(q, p, m) for p in (2, 3, 5, 7, 10007)}
    same = len({tuple(v) for v in rows.values()}) == 1
    print('q=%d m=%d  graded dims of V equal in all chars: %s  %s  total=%d' % (q, m, same, rows[10007], sum(rows[10007])), flush=True)
print('FIN-OK')
