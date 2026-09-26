# regla279c (Grepy el Auditor, 2026-09-25). Hodge characters of the Fermat variety X_m^n (n = 2k) versus pair-type characters.
# A character chi = (chi_0..chi_{n+1}) with all chi_i in Z/m \ 0 and sum 0 is Hodge iff sum_i <t chi_i> = (k+1) m for every t in (Z/m)^x
# ([SK79]; [Ran, Prop. 1.7(iii)]). Pair-type: the multiset splits into pairs {a, -a}. #pair-type = Q_k(m) (Lemma 2.2).
# rank Hdg = #Hodge + 1 and rank L(X) = Q_k(m) + 1, so L(X) = Hdg (given primitivity) iff #Hodge = #pair-type.
# ESTIMATE before running: multisets of size n+2 from m-1 values: largest cell C(52,6) ~ 2e7 is too big; cells chosen <= ~1e6 multisets. < 50 MB, < 5 min.
import itertools, math, sys
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
        if isp and not ish: print('  ERROR: pair-type but not Hodge', m, n, ms)
    return hodge, pair
for m, n in [(3,2),(5,2),(7,2),(3,4),(5,4),(7,4),(11,4),(3,6),(5,6),(3,8),(9,2),(9,4),(25,2),(27,2),(25,4),(49,2),(81,2),(9,6),(121,2)]:
    h, p = cell(m, n)
    v = 'EQUAL' if h == p else 'HODGE > PAIR (extra %d)' % (h - p)
    print('m=%d n=%d k=%d  #Hodge=%d  #pair=%d  gcd(m,(n+1)!)=%d  %s' % (m, n, n // 2, h, p, gcd(m, factorial(n + 1)), v), flush=True)
print('FIN-OK')
