"""GATE G2: |Gamma| by direct enumeration, against the sum over compatible colourings
of the products of block counts (colour-1 block count, N(a,q), N'(a,q)).
Every block count is computed by BRUTE FORCE enumeration (route 1) and, where a formula
exists, by the formula (route 2).  Usage: python3 gate_G2.py m n
"""
import sys, itertools, time
from math import factorial
from fractions import Fraction
from collections import Counter

m, n = int(sys.argv[1]), int(sys.argv[2])
nv = n + 1
t0 = time.time()

# ---------- route 1 for |Gamma|: direct enumeration in (Z/m)^(n+1), a_i <-> exponent ----------
def closed_under_inversion(vals, mod):
    c = Counter(vals)
    return all(c[v] == c[(-v) % mod] for v in c)

def count_Gamma(mod):
    cnt = 0
    for a in itertools.product(range(1, mod), repeat=nv):      # a_i != 1  <->  exponent != 0
        a0 = (-sum(a)) % mod
        if a0 == 0: continue
        if closed_under_inversion(a + (a0,), mod): cnt += 1
    return cnt

Gamma = count_Gamma(m)
print(f"|Gamma| at (m,n)=({m},{n}) by enumeration: {Gamma}")

# ---------- block counts ----------
def colour1_count(e, q):
    """number of e-tuples in mu_q \\ 1 whose multiset is closed under inversion (brute force + formula)."""
    if e % 2: return 0
    brute = sum(1 for a in itertools.product(range(1, q), repeat=e) if closed_under_inversion(a, q)) if q**e <= 3_000_000 else None
    h = (q - 1) // 2
    # e! [x^e] I_0(2x)^h with I_0(2x) = sum x^{2b}/(b!)^2
    # coefficient of x^e in product of h series
    from functools import lru_cache
    coeffs = [Fraction(0)] * (e + 1)
    for b in range(0, e // 2 + 1): coeffs[2 * b] = Fraction(1, factorial(b) ** 2)
    prod = [Fraction(1)] + [Fraction(0)] * e
    for _ in range(h):
        new = [Fraction(0)] * (e + 1)
        for i in range(e + 1):
            if prod[i] == 0: continue
            for j in range(0, e + 1 - i):
                new[i + j] += prod[i] * coeffs[j]
        prod = new
    formula = prod[e] * factorial(e)
    assert formula.denominator == 1
    formula = int(formula)
    if brute is not None: assert brute == formula, (e, q, brute, formula)
    return formula

def N_bal(a, q):
    """balanced bipartite count: brute force and formula sum (a!/prod c_s!)^2."""
    brute = None
    if q ** (2 * a) <= 3_000_000:
        brute = 0
        for xi in itertools.product(range(q), repeat=a):
            cx = Counter(xi)
            for eta in itertools.product(range(q), repeat=a):
                if Counter((-v) % q for v in eta) == cx: brute += 1
    formula = 0
    for comp in itertools.product(range(a + 1), repeat=q):
        if sum(comp) != a: continue
        mult = factorial(a)
        for c in comp: mult //= factorial(c)
        formula += mult * mult
    if brute is not None: assert brute == formula, (a, q, brute, formula)
    return formula

def N_ph(a, q):
    """phantom bipartite count by brute force: (xi,eta) in mu_q^{a+1} x mu_q^a, multiset(eta^-1) subset multiset(xi)."""
    if q ** (2 * a + 1) > 6_000_000:
        return None
    cnt = 0
    for xi in itertools.product(range(q), repeat=a + 1):
        cx = Counter(xi)
        for eta in itertools.product(range(q), repeat=a):
            ce = Counter((-v) % q for v in eta)
            if all(cx[v] >= ce[v] for v in ce): cnt += 1
    return cnt

# ---------- route 2: sum over compatible colourings, for each prime p | m ----------
def factor_primes(x):
    ps, d = [], 2
    while d * d <= x:
        if x % d == 0:
            ps.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: ps.append(x)
    return ps

for p in factor_primes(m):
    q = 1
    while m % (q * p) == 0: q *= p
    r = m // q
    cache1, cacheN, cacheNp = {}, {}, {}
    total = 0
    ncomp = 0
    for c in itertools.product(range(r), repeat=nv):        # colours as exponents mod r
        c0 = (-sum(c)) % r
        col = (c0,) + c
        cnt = Counter(col)
        # compatibility: |E| even, |A_zeta| = |B_zeta|
        E = cnt[0]
        if E % 2: continue
        ok = True
        for z in range(1, r):
            if cnt[z] != cnt[(-z) % r]: ok = False; break
        if not ok: continue
        ncomp += 1
        prod = cache1.get(E)
        if prod is None:
            prod = colour1_count(E, q); cache1[E] = prod
        for z in range(1, (r + 1) // 2):            # representatives z, with -z the partner
            a = cnt[z]                                 # = cnt[-z]
            zero_in = (c0 == z) or (c0 == (r - z) % r)
            if zero_in:
                key = a - 1
                if key not in cacheNp:
                    v = N_ph(key, q)
                    cacheNp[key] = v
                v = cacheNp[key]
                if v is None:
                    raise SystemExit(f"phantom count N'({key},{q}) too large for brute force here")
                prod *= v
            else:
                if a not in cacheN: cacheN[a] = N_bal(a, q)
                prod *= cacheN[a]
        total += prod
    print(f"  p={p} (q={q}, r={r}): compatible colourings {ncomp}; sum_c prod(block counts) = {total}; "
          f"colour-1 counts {dict(sorted(cache1.items()))}, N {dict(sorted(cacheN.items()))}, N' {dict(sorted(cacheNp.items()))}"
          f"   {'MATCH' if total == Gamma else 'MISMATCH'}")
print(f"time {time.time()-t0:.1f}s")
