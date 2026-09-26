# r1cert.py — Fable, Mission 15. Checks the R1 leading-term certificate at q = 3 for k = 1..KMAX.
# For every U subset of [1..n] whose +-1 path (i in U: +1, else -1) has min >= -1, build J, T as in INFORME_15 STEP 1,
# expand y_T * D_J exactly in F_3[y]/(y_i^2) (D_J = prod over pairs (a<b) not containing 0 of (y_b - y_a)),
# and check: nonzero, lex leading monomial (y_1 > ... > y_n) = y_U, coefficient +-1. Also count per degree.
import sys
from math import comb
def cert(n, U):
    # parenthesis matching: U = '(' , not U = ')'
    stack = []; matched = []; unmatched = []
    for i in range(1, n+1):
        if i in U: stack.append(i)
        else:
            if stack: matched.append((stack.pop(), i))
            else: unmatched.append(i)
    if len(unmatched) > 1: return None
    left = sorted(stack)          # unmatched '(' : elements of U
    if unmatched: c = unmatched[0]
    else: c = left.pop()          # odd number left; take one as singleton
    assert len(left) % 2 == 0
    full = [(left[2*i], left[2*i+1]) for i in range(len(left)//2)]
    pairs = matched + full
    T = [a for (a, b) in full] + ([c] if c in U else [])
    return pairs, c, T
def expand(pairs, T):
    poly = {frozenset(T): 1}
    for (a, b) in pairs:
        new = {}
        for m, co in poly.items():
            for v, s in ((b, 1), (a, -1)):
                if v in m: continue
                mm = m | {v}; new[mm] = (new.get(mm, 0) + co*s) % 3
        poly = {m: c for m, c in new.items() if c}
    return poly
def lexkey(m, n): return tuple(1 if i in m else 0 for i in range(1, n+1))
KMAX = int(sys.argv[1])
for k in range(1, KMAX+1):
    n = 2*k+1; cnt = {}
    for mask in range(1 << n):
        U = frozenset(i+1 for i in range(n) if mask >> i & 1)
        h = 0; mn = 0
        for i in range(1, n+1):
            h += 1 if i in U else -1; mn = min(mn, h)
        r = cert(n, U)
        assert (r is not None) == (mn >= -1)
        if r is None: continue
        pairs, c, T = r
        allv = sorted([x for p in pairs for x in p] + [c]); assert allv == list(range(1, n+1))
        poly = expand(pairs, T); assert poly
        lm = max(poly, key=lambda m: lexkey(m, n))
        assert lm == U and poly[lm] in (1, 2), (U, poly)
        cnt[len(U)] = cnt.get(len(U), 0) + 1
    pred = {u: comb(n, u) - comb(n, u+2) for u in range(k, n+1)}
    print('k=%d n=%d LM-count per degree %s pred %s total %d Q=C(2k+2,k+1)=%d %s' % (k, n, [cnt.get(u,0) for u in range(k, n+1)],
          [pred[u] for u in range(k, n+1)], sum(cnt.values()), comb(2*k+2, k+1),
          'OK' if cnt == pred and sum(cnt.values()) == comb(2*k+2, k+1) else 'FAIL'), flush=True)
