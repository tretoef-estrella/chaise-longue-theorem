# k01_counts.py -- Grepy Skies 2. The count |Gamma| for EVEN m, three ways (item T2 / B1).
#  (a) from Definition 1.3 of [DS]: a in (Z/m \ 0)^{2k+1} (additive notation: a_i != 0), such that for some
#      matching J = [[j_0,k_0],...] of {0..2k+1} (j_0 = 0): a_{j_i} + a_{k_i} = 0 for the pairs i >= 1;
#  (b) (2k+2)-tuples in Z/m \ 0 that some perfect matching splits into opposite pairs (brute force);
#  (c) the formula N_{m-1}(2k+2) = (2k+2)! [x^{2k+2}] cosh(x) I_0(2x)^{(m-2)/2};
#  (d) the polynomial displayed in [DS, Remark 4.4] (n = 2, 4, 6), with delta_m = 1 for even m.
# controls that can fail: (e) the value m/2 (i.e. -1) forbidden; (f) the formula with r = m+1 instead of m-1.
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import matchings, Nr
from math import factorial
from fractions import Fraction

def splits(t, m):
    cnt = [0] * m
    for v in t: cnt[v] += 1
    for c in range(1, m):
        if (2 * c) % m == 0:
            if cnt[c] % 2: return False
        elif cnt[c] != cnt[m - c]: return False
    return True

def gamma_DS(k, m, forbid=None):
    n1 = 2 * k + 1
    Js = [[p for p in J if 0 not in p] for J in matchings(list(range(2 * k + 2)))]
    vals = [v for v in range(1, m) if v != forbid]
    c = 0
    for a in itertools.product(vals, repeat=n1):
        for J in Js:
            if all((a[x - 1] + a[y - 1]) % m == 0 for (x, y) in J):
                c += 1; break
    return c

def closed_tuples(k, m):
    N = 2 * k + 2
    return sum(1 for t in itertools.product(range(1, m), repeat=N) if splits(t, m))

def DS_poly(n, m):
    d = 1 if m % 2 == 0 else 0
    if n == 2: return 3 * m * m - 9 * m + 6 + d
    if n == 4: return 15 * m ** 3 - 90 * m * m + 175 * m - 100 + (15 * m - 39) * d
    if n == 6: return 105 * m ** 4 - 1050 * m ** 3 + 3955 * m * m - 6335 * m + 3325 + (210 * m * m - 1302 * m + 2010) * d
    return None

cells = [(1, 4), (1, 6), (1, 8), (1, 10), (1, 12), (1, 14), (2, 4), (2, 6), (2, 8), (3, 4)]
print("k m | (a) DS def | (b) closed tuples | (c) N_{m-1}(2k+2) | (d) DS Remark 4.4 | control (e) -1 forbidden | control (f) N_{m+1}")
allok = True
for (k, m) in cells:
    a = gamma_DS(k, m)
    b = closed_tuples(k, m) if (m - 1) ** (2 * k + 2) <= 3_000_000 else None
    c = Nr(m - 1, 2 * k + 2)
    d = DS_poly(2 * k, m)
    e = gamma_DS(k, m, forbid=m // 2)
    f = Nr(m + 1, 2 * k + 2)
    ok = (a == c) and (b is None or b == c) and (d is None or d == c)
    allok &= ok
    print(k, m, "|", a, "|", b, "|", c, "|", d, "|", e, "(differs: %s)" % (e != c), "|", f, "(differs: %s)" % (f != c), "| agree:", ok)
print("ALL AGREE:", allok)
