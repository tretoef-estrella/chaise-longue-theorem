# regla280 (Grepy el Auditor, 2026-09-25): out-of-sample gate of Aoki 1983 Theorem A (read in the original, Math. Ann. 266 p. 24):
#   B^n_m = D^n_m  <=>  (i) m prime or 4, or (ii) every prime divisor of m is > n+2.
# PREDICTIONS SEALED BEFORE RUNNING (printed first). Reuses cell() of regla279_caracteres_hodge.py.
# ESTIMATE: largest cell (35,4): C(40,6)=3.8e6 multisets, ~2 min, < 50 MB.
import itertools
from math import gcd, factorial
def multinom(c):
    r = factorial(sum(c.values()))
    for v in c.values(): r //= factorial(v)
    return r
def cell(m, n):
    k = n // 2; units = [t for t in range(1, m) if gcd(t, m) == 1]
    hodge = pair = 0
    for ms in itertools.combinations_with_replacement(range(1, m), n + 2):
        if sum(ms) % m: continue
        c = {}
        for a in ms: c[a] = c.get(a, 0) + 1
        w = multinom(c)
        isp = all(c.get(a, 0) == c.get(m - a, 0) for a in c if 2 * a != m) and all(c[a] % 2 == 0 for a in c if 2 * a == m)
        ish = all(sum((t * a) % m for a in ms) == (k + 1) * m for t in units)
        if ish: hodge += w
        if isp: pair += w
    return hodge, pair
def primes(m): return [p for p in range(2, m+1) if m % p == 0 and all(p % d for d in range(2, int(p**.5)+1))]
def aoki(m, n): return (len(primes(m)) == 1 and primes(m)[0] == m) or m == 4 or all(p > n + 2 for p in primes(m))
cells = [(7,6),(11,6),(15,2),(21,2),(35,2),(55,2),(77,2),(45,2),(13,4),(35,4),(15,4)]
print('SEALED PREDICTIONS:', [(m, n, 'EQUAL' if aoki(m, n) else 'EXTRA') for m, n in cells], flush=True)
ok = 0
for m, n in cells:
    h, p = cell(m, n); got = 'EQUAL' if h == p else 'EXTRA'
    pred = 'EQUAL' if aoki(m, n) else 'EXTRA'; ok += got == pred
    print('m=%d n=%d #Hodge=%d #pair=%d got=%s pred=%s %s' % (m, n, h, p, got, pred, 'OK' if got == pred else 'MISMATCH'), flush=True)
print('SCORE %d/%d' % (ok, len(cells))); print('FIN-OK')
