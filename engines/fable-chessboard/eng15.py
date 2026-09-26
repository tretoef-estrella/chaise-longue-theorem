# eng15.py — Fable, Mission 15. Usage: python3 -u eng15.py K Q [LMFILE] [drop]
# Same object as grepy_ds_sum.py: V = (D_J : J)·C, C = F_3[y_1..y_n]/(y_i^{q-1}), n = 2k+1, graded closure.
# Differences: generators are fed in BATCHES into an incremental full RREF (memory ~ rank x cols);
# columns of each degree are sorted lex-DECREASING (y_1 > ... > y_n), so the pivot set of the RREF is the set of
# deglex leading monomials of V. If LMFILE is given, the leading exponent vectors are written there (one per line).
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
def rref(M):
    M = M % 3; r = 0; rows, cols = M.shape; piv = []
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
class Basis:
    def __init__(s, cols): s.B = np.zeros((0, cols), dtype=np.int64); s.piv = []
    def add(s, X):
        if s.B.shape[0]: X = (X - (X[:, s.piv] @ s.B)) % 3
        X = X[np.any(X, axis=1)]
        if not X.shape[0]: return
        R, p2 = rref(X)
        if not R.shape[0]: return
        if s.B.shape[0]: s.B = (s.B - (s.B[:, p2] @ R)) % 3
        s.B = np.vstack([s.B, R]); s.piv = s.piv + p2
def run(k, q, lmfile=None, drop=()):
    n = 2*k+1; r = q-1
    bydeg = {}
    for e in itertools.product(range(r), repeat=n): bydeg.setdefault(sum(e), []).append(e)
    idx = {}
    for d in bydeg:
        bydeg[d].sort(reverse=True)
        for i, e in enumerate(bydeg[d]): idx[e] = i
    Dab = [((-1)**s) % 3 for s in range(q-1)]
    d0 = k*(q-2); cols = len(bydeg[d0]); Bs = Basis(cols); batch = []
    for iJ, J in enumerate(matchings(range(2*k+2))):
        if iJ in drop: continue
        pairs = [(a-1, b-1) for (a, b) in J if a != 0]
        poly = {tuple([0]*n): 1}
        for (a, b) in pairs:
            new = {}
            for e, c in poly.items():
                for s in range(q-1):
                    f = list(e); f[a] += s; f[b] += q-2-s
                    if f[a] >= r or f[b] >= r: continue
                    f = tuple(f); new[f] = (new.get(f, 0) + c*Dab[s]) % 3
            poly = {e: c for e, c in new.items() if c}
        v = np.zeros(cols, dtype=np.int64)
        for e, c in poly.items(): v[idx[e]] = c
        batch.append(v)
        if len(batch) == 4000: Bs.add(np.array(batch)); batch = []
    if batch: Bs.add(np.array(batch))
    ranks = {d0: Bs.B.shape[0]}; lms = {d0: [bydeg[d0][p] for p in Bs.piv]}; V = Bs.B; d = d0
    while d+1 in bydeg and V.shape[0]:
        d += 1; tgt = len(bydeg[d]); src = bydeg[d-1]; Bn = Basis(tgt)
        for i in range(n):
            ok = []; to = []
            for j, e in enumerate(src):
                if e[i] + 1 < r:
                    f = list(e); f[i] += 1; ok.append(j); to.append(idx[tuple(f)])
            if not ok: continue
            X = np.zeros((V.shape[0], tgt), dtype=np.int64); X[:, to] = V[:, ok]; Bn.add(X)
        V = Bn.B; ranks[d] = V.shape[0]; lms[d] = [bydeg[d][p] for p in Bn.piv]
    tot = sum(ranks.values())
    if lmfile:
        with open(lmfile, 'w') as f:
            for d in sorted(lms):
                for e in sorted(lms[d]): f.write(' '.join(map(str, e)) + '\n')
    print('ENG15 k=%d q=%d drop=%s ranks=%s total=%d Q=%d %s' % (k, q, list(drop), [ranks[x] for x in sorted(ranks)], tot, Q(k, q),
          'DS-HOLDS' if tot == Q(k, q) else 'DIFFERS'), flush=True)
if __name__ == '__main__':
    a = sys.argv
    run(int(a[1]), int(a[2]), a[3] if len(a) > 3 and a[3] != '-' else None,
        tuple(int(x) for x in a[4].split(',')) if len(a) > 4 else ())
