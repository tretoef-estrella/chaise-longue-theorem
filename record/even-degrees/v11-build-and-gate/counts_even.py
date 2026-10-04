# regla303 counts_even.py (Grepy Chats, 2 Oct 2026). Numbers for PAPER_OFICIAL_v11:
# (a) Q_k(m) for even m: N! [x^N] cosh(x) I_0(2x)^{(m-2)/2}, against a direct enumeration of Gamma (DS Definition 1.3) in small cells;
# (b) Hodge characters for even m: |B| (all t in (Z/m)^x) and |D| (pair type), by enumeration of multisets.
# Estimate: < 100 MB, < 2 min (largest: m = 12, N = 6: 8008 multisets; m = 8, N = 8: 6435; direct Gamma at (2,8): 7^5 tuples x 15 matchings).
import sys, itertools
from fractions import Fraction
from math import factorial, gcd, comb

def series_mul(a, b, n):
    c = [Fraction(0)] * (n + 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            if i + j > n: break
            c[i + j] += x * y
    return c

def Qeven_or_odd(k, m):
    N = 2 * k + 2
    I0 = [Fraction(0)] * (N + 1)
    for b in range(N // 2 + 1): I0[2 * b] = Fraction(1, factorial(b) ** 2)
    s = [Fraction(1)] + [Fraction(0)] * N
    for _ in range((m - 1) // 2): s = series_mul(s, I0, N)
    if m % 2 == 0:
        ch = [Fraction(1, factorial(i)) if i % 2 == 0 else Fraction(0) for i in range(N + 1)]
        s = series_mul(s, ch, N)
    v = s[N] * factorial(N)
    assert v.denominator == 1
    return int(v)

def matchings(L):
    if not L: yield []; return
    a = L[0]
    for i in range(1, len(L)):
        b = L[i]; rest = L[1:i] + L[i + 1:]
        for M in matchings(rest): yield [(a, b)] + M

def gamma_direct(k, m):
    n1 = 2 * k + 1
    Js = [[p for p in J if 0 not in p] for J in matchings(list(range(2 * k + 2)))]
    c = 0
    for a in itertools.product(range(1, m), repeat=n1):
        if any(all((a[x - 1] + a[y - 1]) % m == 0 for (x, y) in J) for J in Js): c += 1
    return c

def multisets(N, vals):
    # compositions (n_v) with sum N
    def rec(i, left):
        if i == len(vals) - 1:
            yield (left,); return
        for x in range(left + 1):
            for t in rec(i + 1, left - x): yield (x,) + t
    return rec(0, N)

def hodge(k, m):
    N = 2 * k + 2
    vals = list(range(1, m))
    units = [t for t in range(1, m) if gcd(t, m) == 1]
    nB = nD = nA = 0
    for ms in multisets(N, vals):
        if sum(n * v for n, v in zip(ms, vals)) % m: continue
        w = factorial(N)
        for n in ms: w //= factorial(n)
        nA += w
        ok = all(sum(n * ((t * v) % m) for n, v in zip(ms, vals)) == (k + 1) * m for t in units)
        if ok: nB += w
        cnt = dict(zip(vals, ms))
        pair = all(cnt[v] == cnt[m - v] for v in vals if 2 * v != m) and (m % 2 == 1 or cnt[m // 2] % 2 == 0)
        if pair:
            nD += w
            assert ok
    return nA, nB, nD

print('(a) Q_k(m) for even m (and odd m as calibration)')
for m in (3, 5, 9):
    print(' m=%d:' % m, [Qeven_or_odd(k, m) for k in range(1, 5)])
for m in (4, 6, 8, 10, 12, 14, 16, 18, 20):
    print(' m=%d:' % m, [Qeven_or_odd(k, m) for k in range(0, 6)])
print(' direct Gamma (DS Def. 1.3):', {(k, m): gamma_direct(k, m) for (k, m) in [(1, 4), (1, 6), (1, 8), (1, 10), (2, 4), (2, 6), (2, 8), (3, 4)]})
print(' formula                   :', {(k, m): Qeven_or_odd(k, m) for (k, m) in [(1, 4), (1, 6), (1, 8), (1, 10), (2, 4), (2, 6), (2, 8), (3, 4)]})
print('(b) Hodge characters: (k, m): |A|, |B|, |D|, |B|-|D|, Q_k(m)')
for (k, m) in [(1, 3), (1, 5), (1, 9), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4), (1, 6), (2, 6), (3, 6), (1, 8), (2, 8), (3, 8), (1, 10), (2, 10), (1, 12), (2, 12), (1, 14), (1, 16), (1, 18), (1, 20)]:
    nA, nB, nD = hodge(k, m)
    print(' (%d,%d): %d %d %d  diff %d  Q %d  %s' % (k, m, nA, nB, nD, nB - nD, Qeven_or_odd(k, m), 'D=Q OK' if nD == Qeven_or_odd(k, m) else 'MISMATCH'))
