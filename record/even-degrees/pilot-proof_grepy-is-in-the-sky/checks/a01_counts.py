# a01_counts.py — pilot. Leg A / R1: |Gamma| for even m by three independent routes.
#  (1) the definition of [DS]: tuples a in (Z/m \ 0)^(2k+1) for which some matching J has a_j + a_k = 0 on the k pairs avoiding 0
#  (2) brute force: (2k+2)-tuples in Z/(m-1)-with-negation ... replaced by a direct model: a set of m-1 elements with an
#      involution with exactly one fixed point (Z/(m-1) with x -> -x), closed tuples, fixed value used an even number of times
#  (3) the formula N_{m-1}(2k+2) = (2k+2)! [x^(2k+2)] cosh(x) I_0(2x)^((m-2)/2)
# Negative controls (v2; the control of v1, exp(x) in place of cosh(x), could not fail: for even n the odd part of exp contributes nothing):
#   (c1) the value -1 forbidden:  Q^[h](2k+2) = (2k+2)! [x^(2k+2)] I_0(2x)^h, h = (m-2)/2      -> must be smaller
#   (c2) -1 treated as an ordinary class (as if m+1 were the odd degree): Q^[h+1](2k+2)          -> must be larger
import sys, itertools
from eng import matchings, N_odd, closed_tuples_bruteforce, egf_coeff, series_I0, Q_free
from fractions import Fraction
from math import factorial

def gamma_def(k, m):
    n1 = 2 * k + 1
    Js = [[(a, b) for (a, b) in J if a != 0] for J in matchings(range(n1 + 1))]
    cnt = 0
    for a in itertools.product(range(1, m), repeat=n1):
        for J in Js:
            if all((a[x - 1] + a[y - 1]) % m == 0 for (x, y) in J):
                cnt += 1
                break
    return cnt

cells = [(1, 4), (1, 6), (1, 8), (1, 10), (1, 12), (1, 16), (1, 32), (2, 4), (2, 6), (2, 8), (2, 10), (3, 4)]
allok = True
for (k, m) in cells:
    n = 2 * k + 2
    g = gamma_def(k, m)
    f = N_odd(m - 1, n)
    b = closed_tuples_bruteforce(m - 1, n) if (m - 1) ** n <= 3_000_000 else None
    c1 = Q_free((m - 2) // 2, n); c2 = Q_free(m // 2, n)
    ok = (g == f) and (b is None or b == f)
    allok &= ok
    print(f"k={k} m={m}: |Gamma| by definition={g}  formula N_(m-1)(2k+2)={f}  brute closed tuples={b}  agree={ok}   [controls: without -1: {c1} (<: {c1 < g}); -1 as an ordinary class: {c2} (>: {c2 > g})]", flush=True)
print("ALL AGREE" if allok else "SOME DISAGREE")
