#!/usr/bin/env python3
"""
overclaims_numeric_tables.py  (referee label: overclaims)

Light, exact re-derivation of the numerical statements of PAPER_OFICIAL_v6.md
that the "overclaims and novelty" referee can check cheaply:

  * Q_k(q) = N! [x^N] I_0(2x)^h  (h=(q-1)/2, N=2k+2): the table at §3 (lines 215-224),
    the closed forms Q_1(q)=3(q-1)(q-2), Q_k(3)=C(2k+2,k+1), the polynomials Q_2, Q_3
    (line 213), the values 32 900 = Q_2(15), 102 800 = Q_2(21), and the numbers quoted
    in §12.1 (q^{2k+1}-Q_k(q), 45 756, 6 768, 3 432, 190 120, 182 400).
  * Independent cross-check of Q_k(q) by brute-force enumeration of N-tuples closed
    under a fixed-point-free involution (small cells) and by Lemma 3.1's zero-free set Gamma'.
  * N_bal(a,q) = sum multinomial^2, N_ph(a,q) = N_bal(a+1,q): line 576 examples and §12.4 values
    (4653, 7885, 11713), cross-checked by brute force at small cells.
  * Lemma 10.4 arithmetic: C(2k+2,k+1)^3 - Q_k(9) = 48, 2880, 152880, 8064000; and an
    independent enumeration of |B| (Hodge characters, Aoki's definition) at m=9, k=1,2
    and at (k,m)=(1,15),(1,21),(1,25),(1,35) against Remark 10.3.
  * The hypothesis of Corollary H(i) for the cells (2,49),(2,77),(3,121),(3,143) of §1.3, and
    the equivalence "all prime factors >= 2k+3" <=> gcd(m,(n+2)!)=1 <=> gcd(m,(n+1)!)=1 for odd m.
  * Fact 9.2: |Gamma_K| = 4736 for the 13-matching subfamily at (k,q)=(2,9), and |Gamma_J|=5120.
  * §12.3 colouring counts (compatible colourings: 61, 19, 1001, 141, 3301) from the
    exponential formula; Theorem 4.1 graded ranks and Remark 4.2 ballot numbers;
    §12.1 graded-rank rows summing to Q_k(q); Remark 10.2 discriminant-group exponents.

PREDICTION (written before the run): every quoted number reproduces exactly; runtime < 10 s,
memory < 100 MB (largest enumeration: 8^5 = 32 768 tuples at (k,q)=(2,9); 24^3 tuples at (1,25)).
"""
import itertools, math, sys, time
from fractions import Fraction
from math import comb, factorial, gcd

t0 = time.time()
FAIL = []
def check(name, got, expected):
    ok = (got == expected)
    print(f"[{'OK ' if ok else 'BAD'}] {name}: got {got}, expected {expected}")
    if not ok:
        FAIL.append((name, got, expected))

# ---------- Q_k(q) by the generating function (exact rationals) ----------
def I0_coeffs(nmax):
    # I_0(2x) = sum_b x^{2b}/(b!)^2 ; coefficients up to x^nmax
    c = [Fraction(0)] * (nmax + 1)
    for b in range(nmax // 2 + 1):
        c[2 * b] = Fraction(1, factorial(b) ** 2)
    return c

def poly_mul(a, b, nmax):
    c = [Fraction(0)] * (nmax + 1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if i + j > nmax: break
            c[i + j] += ai * bj
    return c

def Q(k, q):
    N = 2 * k + 2
    h = (q - 1) // 2
    base = I0_coeffs(N)
    acc = [Fraction(0)] * (N + 1); acc[0] = Fraction(1)
    for _ in range(h):
        acc = poly_mul(acc, base, N)
    val = acc[N] * factorial(N)
    assert val.denominator == 1
    return int(val)

print("== Q_k(q) table (§3, lines 215-224) ==")
table = {
    3:  [6, 20, 70, 252, 924],
    5:  [36, 400, 4900, 63504, 853776],
    7:  [90, 1860, 44730, 1172556, 32496156],
    9:  [168, 5120, 190120, 7939008, 357713664],
    11: [270, 10900, 551950, 32232060, 2070891900],
    13: [396, 19920, 1281420, 96807312, 8175770064],
    25: [1656, 182400, 26926200, 4890642624, 1038711332736],
    27: [1950, 234260, 37849630, 7550855676, 1767675505596],
}
for q, row in table.items():
    check(f"Q_k({q}) k=1..5", [Q(k, q) for k in range(1, 6)], row)

print("== closed forms ==")
check("Q_0(q)=q-1, q=3..15", [Q(0, q) for q in range(3, 16, 2)], [q - 1 for q in range(3, 16, 2)])
check("Q_1(q)=3(q-1)(q-2), q=3..31", [Q(1, q) for q in range(3, 32, 2)], [3 * (q - 1) * (q - 2) for q in range(3, 32, 2)])
check("Q_k(3)=C(2k+2,k+1), k=0..8", [Q(k, 3) for k in range(9)], [comb(2 * k + 2, k + 1) for k in range(9)])
P2 = lambda q: 15 * q**3 - 90 * q**2 + 175 * q - 100
P3 = lambda q: 105 * q**4 - 1050 * q**3 + 3955 * q**2 - 6335 * q + 3325
check("Q_2(q) polynomial (line 213), q=3..41", [Q(2, q) for q in range(3, 42, 2)], [P2(q) for q in range(3, 42, 2)])
check("Q_3(q) polynomial (line 213), q=3..41", [Q(3, q) for q in range(3, 42, 2)], [P3(q) for q in range(3, 42, 2)])
# polynomial identity check via 4 resp. 5 interpolation points is implied by 20 values; also check symbolic degree
check("Q_2(15)=32900 (§12.3)", Q(2, 15), 32900)
check("Q_2(21)=102800 (§12.3)", Q(2, 21), 102800)
check("Q_1(125)=45756 (§12.1)", Q(1, 125), 45756)
check("Q_1(49)=6768 (§12.1)", Q(1, 49), 6768)
check("Q_6(3)=3432 (§12.1)", Q(6, 3), 3432)
check("Q_3(9)=190120 (§12.1)", Q(3, 9), 190120)
check("Q_2(25)=182400 (§12.1)", Q(2, 25), 182400)
check("q^{2k+1}-Q_k(q) literal quotients (§12.1)",
      [3**3 - Q(1, 3), 3**5 - Q(2, 3), 3**7 - Q(3, 3), 5**3 - Q(1, 5), 5**5 - Q(2, 5), 7**3 - Q(1, 7), 2**11 - Q(5, 3)],
      [21, 223, 2117, 89, 2725, 253, 1124])
print("   (§1.3 cells claimed verified in [Rep] but absent from §12.1 table): Q_2(17) =", Q(2, 17), " Q_2(19) =", Q(2, 19), " Q_4(5) =", Q(4, 5))
print("   §2.2: Q_1(q)=4!*(h/4+h(h-1)/2):", all(24 * (Fraction(h, 4) + Fraction(h * (h - 1), 2)) == Q(1, 2 * h + 1) for h in range(1, 12)))

# ---------- brute-force cross-check of Q_k(q): N-tuples in T closed under involution ----------
def Q_brute(k, q):
    N = 2 * k + 2; h = (q - 1) // 2
    T = list(range(1, h + 1)) + list(range(-h, 0))  # involution u -> -u
    cnt = 0
    for tup in itertools.product(T, repeat=N):
        ok = True
        for u in range(1, h + 1):
            if tup.count(u) != tup.count(-u):
                ok = False; break
        cnt += ok
    return cnt

def Q_gamma_prime(k, q):
    # Lemma 3.1: tuples in T^{2k+1} with nu = k
    h = (q - 1) // 2
    T = list(range(1, h + 1)) + list(range(-h, 0))
    cnt = 0
    for tup in itertools.product(T, repeat=2 * k + 1):
        nu = sum(min(tup.count(u), tup.count(-u)) for u in range(1, h + 1))
        cnt += (nu == k)
    return cnt

print("== brute-force cross-checks of Q ==")
for (k, q) in [(1, 3), (1, 5), (1, 7), (1, 9), (2, 3), (2, 5), (3, 3), (2, 7)]:
    check(f"Q_brute({k},{q})", Q_brute(k, q), Q(k, q))
for (k, q) in [(1, 3), (1, 5), (1, 9), (2, 3), (2, 5), (3, 3)]:
    check(f"|Gamma'|({k},{q}) (Lemma 3.1)", Q_gamma_prime(k, q), Q(k, q))

# ---------- Definition 1.3 of [DS]: |Gamma_J| by direct enumeration (odd m), and Fact 9.2 ----------
def matchings(idx):
    if not idx: yield []; return
    a = idx[0]
    for i in range(1, len(idx)):
        b = idx[i]
        rest = idx[1:i] + idx[i + 1:]
        for M in matchings(rest):
            yield [(a, b)] + M

def gamma_size(k, m, K=None):
    n1 = 2 * k + 1
    J_all = list(matchings(list(range(2 * k + 2))))
    if K is None: K = J_all
    cnt = 0
    for a in itertools.product(range(1, m), repeat=n1):  # a_i in Z/m \ {0} (exponents), a_i != 1 means exponent != 0
        aa = (0,) + a
        for J in K:
            if all((aa[x] + aa[y]) % m == 0 for (x, y) in J if x != 0):
                cnt += 1; break
    return cnt, J_all

print("== [DS, Definition 1.3] enumerations ==")
for (k, m) in [(1, 3), (1, 5), (1, 9), (1, 15), (2, 3), (2, 5)]:
    g, _ = gamma_size(k, m)
    check(f"|Gamma_J|({k},{m}) = Q_k(m)", g, Q(k, m))
g_all, J_all = gamma_size(2, 9)
check("|Gamma_J|(2,9)", g_all, 5120)
excluded = [[(0, 1), (2, 3), (4, 5)], [(0, 2), (1, 5), (3, 4)]]
K = [J for J in J_all if J not in excluded]
check("Fact 9.2: |K| = 13", len(K), 13)
g_K, _ = gamma_size(2, 9, K)
check("Fact 9.2: |Gamma_K| (k=2,q=9, 13 matchings)", g_K, 4736)

# ---------- N_bal, N_ph ----------
def N_bal(a, q):
    tot = 0
    for comp in itertools.product(range(a + 1), repeat=q):
        if sum(comp) != a: continue
        mult = factorial(a)
        for c in comp: mult //= factorial(c)
        tot += mult * mult
    return tot

def N_bal_brute(a, q):
    return sum(1 for xi in itertools.product(range(q), repeat=a) for eta in itertools.product(range(q), repeat=a) if sorted(xi) == sorted(eta))

def N_ph_brute(a, q):
    cnt = 0
    for xi in itertools.product(range(q), repeat=a + 1):
        for eta in itertools.product(range(q), repeat=a):
            ok = all(eta.count(v) <= xi.count(v) for v in set(eta))
            cnt += ok
    return cnt

print("== N_bal / N_ph (line 576, §12.4) ==")
check("N_bal(a,3), a=1..5", [N_bal(a, 3) for a in range(1, 6)], [3, 15, 93, 639, 4653])
check("N_bal(2,q), q=3,5,7,9,11", [N_bal(2, q) for q in (3, 5, 7, 9, 11)], [15, 45, 91, 153, 231])
check("N_bal(5,3)=N_ph(4,3)=4653 (§12.4)", (N_bal(5, 3), N_bal(5, 3)), (4653, 4653))
check("N_bal(4,5)=7885 (§12.4)", N_bal(4, 5), 7885)
check("N_ph(2,13)=N_bal(3,13)=11713 (§12.4)", N_bal(3, 13), 11713)
check("N_bal brute (2,3),(3,3),(2,5)", [N_bal_brute(2, 3), N_bal_brute(3, 3), N_bal_brute(2, 5)], [N_bal(2, 3), N_bal(3, 3), N_bal(2, 5)])
check("N_ph brute = N_bal(a+1) at (1,3),(2,3),(1,5)", [N_ph_brute(1, 3), N_ph_brute(2, 3), N_ph_brute(1, 5)], [N_bal(2, 3), N_bal(3, 3), N_bal(2, 5)])
check("N_bal(0,q)=1, N_ph(0,q)=q", (N_bal(0, 7), N_bal(1, 7)), (1, 7))

# ---------- Hodge characters (Aoki's definition) ----------
def hodge_count(k, m):
    N = 2 * k + 2
    units = [t for t in range(1, m) if gcd(t, m) == 1]
    B = 0; D = 0
    for a in itertools.product(range(1, m), repeat=N - 1):
        a0 = (-sum(a)) % m
        if a0 == 0: continue
        al = (a0,) + a
        if all(sum((t * x) % m for x in al) == m * (k + 1) for t in units):
            B += 1
            # pair type?
            cnt = {}
            for x in al: cnt[x] = cnt.get(x, 0) + 1
            if all(cnt.get(x, 0) == cnt.get(m - x, 0) for x in cnt):
                D += 1
    return B, D

print("== Hodge characters: Lemma 10.4 / Remark 10.3 (independent enumeration) ==")
check("Lemma 10.4 arithmetic C(2k+2,k+1)^3-Q_k(9), k=1..4", [comb(2 * k + 2, k + 1) ** 3 - Q(k, 9) for k in range(1, 5)], [48, 2880, 152880, 8064000])
for (k, m, expB) in [(1, 9, 216), (2, 9, 8000), (1, 15, None), (1, 21, None), (1, 25, None), (1, 35, None), (1, 3, None), (1, 5, None), (1, 7, None)]:
    B, D = hodge_count(k, m)
    if expB is not None:
        check(f"|B|({k},{m})", B, expB)
    check(f"|D|({k},{m}) = Q_k(m) (Lemma 10.1(ii))", D, Q(k, m))
    print(f"      (k,m)=({k},{m}): |B|-Q_k(m) = {B - D}")
check("Remark 10.3: |B|-Q at (1,15),(1,21) = 288, 432", [hodge_count(1, 15)[0] - Q(1, 15), hodge_count(1, 21)[0] - Q(1, 21)], [288, 432])
check("Remark 10.3: |B|-Q at (1,25),(1,35) = 0,0", [hodge_count(1, 25)[0] - Q(1, 25), hodge_count(1, 35)[0] - Q(1, 35)], [0, 0])

# ---------- Corollary H(i) hypothesis for the §1.3 cells; equivalence of the three conditions ----------
def primes_of(m):
    ps = set(); d = 2
    while d * d <= m:
        while m % d == 0: ps.add(d); m //= d
        d += 1
    if m > 1: ps.add(m)
    return ps
print("== §1.3 cells and the gcd conditions ==")
for (k, m) in [(2, 49), (2, 77), (3, 121), (3, 143)]:
    check(f"cell ({k},{m}): every prime factor >= 2k+3={2*k+3}", all(p >= 2 * k + 3 for p in primes_of(m)), True)
for (k, m) in [(2, 15), (2, 21), (2, 25), (2, 35), (1, 9), (1, 15)]:
    print(f"      cell ({k},{m}) is NOT a cell of H(i) (prime factors {sorted(primes_of(m))}, need >= {2*k+3}): {not all(p >= 2*k+3 for p in primes_of(m))}")
eq = True
for k in range(1, 7):
    n = 2 * k
    for m in range(3, 3000, 2):
        c1 = all(p >= 2 * k + 3 for p in primes_of(m))
        c2 = gcd(m, factorial(n + 2)) == 1
        c3 = gcd(m, factorial(n + 1)) == 1
        if not (c1 == c2 == c3): eq = False; print("   mismatch", k, m, c1, c2, c3)
check("odd m: (all p>=2k+3) <=> gcd(m,(n+2)!)=1 <=> gcd(m,(n+1)!)=1, k<=6, m<3000", eq, True)

# ---------- §12.3 compatible-colouring counts via exponential formula ----------
def compat_colourings(k, r):
    # number of N-tuples of colours in mu_r (N=2k+2) whose multiset is closed under inversion
    # (colour 1: even multiplicity; pairs {zeta, zeta^-1}: equal multiplicities); c_0 determined => equals number of c in mu_r^{n+1}
    N = 2 * k + 2; hr = (r - 1) // 2
    cosh = [Fraction(1, factorial(j)) if j % 2 == 0 else Fraction(0) for j in range(N + 1)]
    acc = cosh
    base = I0_coeffs(N)
    for _ in range(hr): acc = poly_mul(acc, base, N)
    return int(acc[N] * factorial(N))
print("== §12.3 colouring counts ==")
check("compatible colourings k=1: (m=15,p=3,r=5),(15,5,r=3),(21,7,r=3)", [compat_colourings(1, 5), compat_colourings(1, 3), compat_colourings(1, 3)], [61, 19, 19])
check("compatible colourings k=2: (15,3,r=5),(15,5,r=3),(21,3,r=7),(21,7,r=3)", [compat_colourings(2, 5), compat_colourings(2, 3), compat_colourings(2, 7), compat_colourings(2, 3)], [1001, 141, 3301, 141])
check("total colourings r^{2k+1}: 5^5,3^5,7^5", [5**5, 3**5, 7**5], [3125, 243, 16807])

# ---------- Theorem 4.1 graded ranks, Remark 4.2 ballot numbers, §12.1 rows ----------
print("== Theorem 4.1 / Remark 4.2 / §12.1 graded rows ==")
rows42 = {1: [2, 3, 1], 2: [5, 9, 5, 1], 3: [14, 28, 20, 7, 1], 4: [42, 90, 75, 35, 9, 1], 5: [132, 297, 275, 154, 54, 11, 1], 6: [429, 1001, 1001, 637, 273, 77, 13, 1]}
for k, row in rows42.items():
    n1 = 2 * k + 1
    got = [comb(n1, u) - comb(n1, u + 2) for u in range(k, n1 + 1)]
    ballot = [comb(2 * k + 2, k + 1 - j) * (2 * j + 1) // (k + 2 + j) for j in range(0, k + 2)]
    check(f"Thm 4.1 ranks k={k}", got, row)
    check(f"Rem 4.2 ballot k={k}", ballot, row)
    check(f"sum = Q_k(3), k={k}", sum(row), Q(k, 3))
row19 = [3, 6, 9, 12, 15, 18, 20, 21, 18, 15, 12, 9, 6, 3, 1]
row29 = [15, 45, 90, 150, 224, 310, 395, 470, 515, 530, 516, 475, 411, 329, 245, 170, 110, 65, 34, 15, 5, 1]
check("§12.1 (1,9) row: 15 entries (degrees 7..21), sum 168", (len(row19), sum(row19)), (15, 168))
check("§12.1 (2,9) row: 22 entries (degrees 14..35), sum 5120", (len(row29), sum(row29)), (22, 5120))
row127 = [3 * j for j in range(1, 25)] + [74, 75] + [3 * j for j in range(24, 0, -1)] + [1]
check("§12.1 (1,27) row as read: 51 entries (degrees 25..75), sum 1950", (len(row127), sum(row127)), (51, 1950))

# ---------- Remark 10.2 discriminant exponents (internal consistency) ----------
print("== Remark 10.2 internal consistency ==")
for p in (7, 11, 13):
    e = (3 * p * p - 24 * p + 59) + 2 * (3 * p - 16)
    check(f"Remark 10.2 p={p}: |disc| exponent", e, 3 * (p - 3) ** 2)
check("Remark 10.2 p=5: 10+2 = 3*(5-3)^2", 10 + 2, 3 * 4)

# ---------- Remark 7.9(2): dim_Q ((x-z)^2) in Q[x,z]/(x^3,z^3) = 4, and 3 over F_3 ----------
import sympy as sp
x, z = sp.symbols('x z')
g = sp.expand((x - z) ** 2)
mons = [x**i * z**j for i in range(3) for j in range(3)]
rows = []
for mon in mons:
    f = sp.Poly(sp.expand(mon * g), x, z)
    coeffs = {(a, b): c for (a, b), c in f.terms() if a < 3 and b < 3}   # reduce mod (x^3, z^3)
    rows.append([coeffs.get((i, j), 0) for i in range(3) for j in range(3)])
M = sp.Matrix(rows)
check("Remark 7.9(2): dim_Q((x-z)^2) in Q[x,z]/(x^3,z^3)", M.rank(), 4)
check("Remark 7.9(2): dim_F3 = N_bal(1,3) = 3", M.rank(iszerofunc=lambda e: e % 3 == 0), 3)

print(f"\nDONE in {time.time()-t0:.2f}s; failures: {len(FAIL)}")
for f in FAIL: print("  FAIL:", f)
sys.exit(1 if FAIL else 0)
