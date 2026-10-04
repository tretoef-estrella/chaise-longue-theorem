# F1: for k >= 1, gcd(m,(n+1)!)=1  <=>  gcd(m,(n+2)!)=1  <=>  every prime factor of m >= 2k+3 (= Aoki: > n+2); control k = 0.
from math import gcd, factorial
from sympy import primefactors
mism = {}; tested = 0
for k in range(0, 31):
    n = 2*k
    f1, f2 = factorial(n+1), factorial(n+2)
    for m in range(3, 3001):
        a = gcd(m, f1) == 1; b = gcd(m, f2) == 1; c = all(p >= 2*k+3 for p in primefactors(m))
        tested += 1
        if not (a == b == c): mism.setdefault(k, []).append((m, a, b, c))
print('tested pairs (k,m):', tested)
for k, L in mism.items(): print('k =', k, ': mismatches', len(L), 'first', L[:3])
print('mismatches for k >= 1:', sum(len(L) for k, L in mism.items() if k >= 1))
