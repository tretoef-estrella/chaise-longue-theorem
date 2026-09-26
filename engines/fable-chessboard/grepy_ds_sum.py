# grepy_ds_sum.py — auditor (Grepy el Lector), 2026-09-24. Usage: python3 -u grepy_ds_sum.py K Q [comma-list of removed matching indices].
#   DS <=> dim_{F_3} (D_J : J)·C = Q_k(q),  C = F_3[y_1..y_{2k+1}]/(y_i^{q-1}),
#   D_J = prod over the pairs {j,l} of J not containing 0 of D(y_j,y_l),  D(a,b) = sum_{s=0}^{q-2} (-1)^s a^s b^{q-2-s}  (= (b^{q-1}-a^{q-1})/(a+b)).
#   At q = 3: D(a,b) = b - a.
# The ideal is generated in the single degree k(q-2); graded closure V_{d+1} = sum_i y_i V_d.  Prints rank per degree and the total.
import sys, itertools, numpy as np
from math import factorial
from fractions import Fraction
def matchings(s):
    s = list(s)
    if not s: yield []; return
    a = s[0]
    for i in range(1, len(s)):
        for m in matchings(s[1:i] + s[i+1:]): yield [(a, s[i])] + m
def Q(k, q):
    n = 2*k+2; h = (q-1)//2
    I = [Fraction(1, factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    p = [Fraction(1)] + [Fraction(0)]*n
    for _ in range(h): p = [sum(p[j]*I[i-j] for j in range(i+1)) for i in range(n+1)]
    return int(p[n]*factorial(n))
def rref_mod3(M):
    M = M.copy() % 3; r = 0; rows, cols = M.shape; piv = []
    for c in range(cols):
        if r == rows: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        p = r + nz[0]
        if p != r: M[[r, p]] = M[[p, r]]
        if M[r, c] == 2: M[r] = (2*M[r]) % 3
        col = M[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr): M[nzr] = (M[nzr] - np.outer(col[nzr], M[r])) % 3
        piv.append(c); r += 1
    return M[:r], piv
def run(k, q, drop=()):
    n1 = 2*k+1; r = q-1
    mons = {}; bydeg = {}
    for e in itertools.product(range(r), repeat=n1):
        d = sum(e); bydeg.setdefault(d, []).append(e)
    for d in bydeg:
        for i, e in enumerate(bydeg[d]): mons[e] = (d, i)
    Dab = [((-1)**s) % 3 for s in range(q-1)]   # coefficient of a^s b^{q-2-s}
    d0 = k*(q-2)
    rows = []
    for iJ, J in enumerate(matchings(range(2*k+2))):
        if iJ in drop: continue
        pairs = [(a-1, b-1) for (a, b) in J if a != 0]
        poly = {tuple([0]*n1): 1}
        for (a, b) in pairs:
            new = {}
            for e, c in poly.items():
                for s in range(q-1):
                    f = list(e); f[a] += s; f[b] += q-2-s
                    if f[a] >= r or f[b] >= r: continue
                    f = tuple(f); new[f] = (new.get(f, 0) + c*Dab[s]) % 3
            poly = {e: c for e, c in new.items() if c}
        v = np.zeros(len(bydeg[d0]), dtype=np.int64)
        for e, c in poly.items(): v[mons[e][1]] = c
        rows.append(v)
    V, _ = rref_mod3(np.array(rows)); ranks = {d0: V.shape[0]}; d = d0
    while True:
        d += 1
        if d not in bydeg or V.shape[0] == 0: break
        tgt = len(bydeg[d]); src = bydeg[d-1]; blocks = []
        for i in range(n1):
            idx = []; ok = []
            for j, e in enumerate(src):
                if e[i] + 1 < r:
                    f = list(e); f[i] += 1; idx.append(mons[tuple(f)][1]); ok.append(j)
            if not ok: continue
            B = np.zeros((V.shape[0], tgt), dtype=np.int64); B[:, idx] = V[:, ok]; blocks.append(B)
        V, _ = rref_mod3(np.vstack(blocks)); ranks[d] = V.shape[0]
    tot = sum(ranks.values())
    if drop: print('SUBFAMILY drop=%s (Q below is the FULL-family count)' % (list(drop),))
    print('SUMFORM k=%d q=%d ranks=%s total=%d Q=%d %s' % (k, q, [ranks[x] for x in sorted(ranks)], tot, Q(k, q), 'DS-HOLDS' if tot == Q(k, q) else 'DIFFERS'), flush=True)
if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), tuple(int(x) for x in sys.argv[3].split(',')) if len(sys.argv) > 3 else ())
