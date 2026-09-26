#!/usr/bin/env python3
"""Hostile re-read: cheap numerical claims of PAPER_OFICIAL_v6.md re-derived from scratch.
Prediction: every check prints AGREES. Expected < 30 s, < 60 MB.
Items:
 1. Q_k(q) = N! [x^N] I_0(2x)^h  vs table §3 and the polynomials Q_2, Q_3 (DS Remark 4.4), Q_1 = 3(q-1)(q-2).
 2. Q_k(q) equals the direct count of N-tuples in a (q-1)-set closed under a fixed-point-free involution (Lemma 2.2), k<=3, small q.
 3. N_bal(a,3) = 3,15,93,639,4653 ; N_bal(2,q) = 15,45,91,153,231 ; N_ph(a,q) = N_bal(a+1,q) by brute force (Lemma 7.2(iii)).
 4. Ballot numbers of Remark 4.2(1): C(n',k+j)-C(n',k+j+2) = C(2k+2,k+1-j)(2j+1)/(k+2+j), and their sums = Q_k(3).
 5. P_2(3) = 141 (F_3-points of the union of matching spaces in F_3^6), Q_2(3) = 20.
 6. Fact 9.2: |Gamma_K| = 4736 for the 13-matching subfamily at (k,q)=(2,9) [DS Definition 1.3, literal].
 7. Compatible colourings (§6.3): counts at (k,r) = (2,5),(2,3),(2,7),(1,5),(1,3) vs 1001,141,3301,61,19 (§12.3).
 8. Lemma 10.4: delta values, sign bijection, matrix M, det M = 81; |B| = C(N,N/2)^3 for k=1,2 by direct enumeration.
 9. Corollary W(ii): |Gamma_K| for K = J(1,2) at m = 5, 9 equals Q_1(m)(m-1) = 144, 1344 (DS Definition 1.3, literal).
10. Lemma 6.8 at k=1: |Gamma_J| (literal) equals sum over compatible colourings of block counts N_1 * prod N_zeta, for m = 15, 21.
"""
import itertools, math, sys
from fractions import Fraction
from collections import Counter

ok_all = True
def report(name, got, exp):
    global ok_all
    s = "AGREES" if got == exp else "DISAGREES"
    if got != exp: ok_all = False
    print(f"[{s}] {name}: got {got} expected {exp}")

# ---------- 1. Q_k(q) ----------
def Qk(k, q):
    h = (q - 1) // 2
    N = 2 * k + 2
    # series I_0(2x) = sum x^{2b}/(b!)^2, truncated at degree N
    ser = [Fraction(0)] * (N + 1)
    for b in range(N // 2 + 1):
        ser[2 * b] = Fraction(1, math.factorial(b) ** 2)
    res = [Fraction(0)] * (N + 1); res[0] = Fraction(1)
    for _ in range(h):
        new = [Fraction(0)] * (N + 1)
        for i, a in enumerate(res):
            if a == 0: continue
            for j, b in enumerate(ser):
                if i + j <= N and b != 0:
                    new[i + j] += a * b
        res = new
    v = res[N] * math.factorial(N)
    assert v.denominator == 1
    return int(v)

table = {3: [6, 20, 70, 252, 924], 5: [36, 400, 4900, 63504, 853776], 7: [90, 1860, 44730, 1172556, 32496156],
         9: [168, 5120, 190120, 7939008, 357713664], 11: [270, 10900, 551950, 32232060, 2070891900],
         13: [396, 19920, 1281420, 96807312, 8175770064], 25: [1656, 182400, 26926200, 4890642624, 1038711332736],
         27: [1950, 234260, 37849630, 7550855676, 1767675505596]}
for q, row in table.items():
    report(f"table §3 row q={q}", [Qk(k, q) for k in range(1, 6)], row)
for q in [3, 5, 7, 9, 11, 13, 15, 21, 25, 27, 45]:
    report(f"Q_1({q}) = 3(q-1)(q-2)", Qk(1, q), 3 * (q - 1) * (q - 2))
    report(f"Q_2({q}) polynomial", Qk(2, q), 15 * q**3 - 90 * q**2 + 175 * q - 100)
    report(f"Q_3({q}) polynomial", Qk(3, q), 105 * q**4 - 1050 * q**3 + 3955 * q**2 - 6335 * q + 3325)
for k in range(1, 7):
    report(f"Q_{k}(3) = C(2k+2,k+1)", Qk(k, 3), math.comb(2 * k + 2, k + 1))
report("Q_2(15) (§12.3)", Qk(2, 15), 32900)
report("Q_2(21) (§12.3)", Qk(2, 21), 102800)
report("Q_1(125)", Qk(1, 125), 45756)

# ---------- 2. direct count of closed N-tuples ----------
def closed_count(k, q):
    h = (q - 1) // 2
    N = 2 * k + 2
    # elements 0..q-2, involution u -> u^h pairs: (2i, 2i+1)
    cnt = 0
    for tup in itertools.product(range(q - 1), repeat=N):
        c = Counter(tup)
        if all(c[2 * i] == c[2 * i + 1] for i in range(h)):
            cnt += 1
    return cnt
for (k, q) in [(1, 3), (1, 5), (1, 7), (2, 3), (2, 5), (3, 3)]:
    report(f"closed {2*k+2}-tuples in T (|T|={q-1}) = Q_{k}({q})", closed_count(k, q), Qk(k, q))

# ---------- 3. N_bal, N_ph ----------
def compositions(a, parts):
    if parts == 1: yield (a,); return
    for first in range(a + 1):
        for rest in compositions(a - first, parts - 1): yield (first,) + rest
def N_bal_formula(a, q):
    tot = 0
    for comp in compositions(a, q):
        mult = math.factorial(a)
        for c in comp: mult //= math.factorial(c)
        tot += mult * mult
    return tot
def N_bal_brute(a, q):
    return sum(1 for xi in itertools.product(range(q), repeat=a) for eta in itertools.product(range(q), repeat=a)
               if Counter(xi) == Counter(eta))
def N_ph_brute(a, q):
    return sum(1 for xi in itertools.product(range(q), repeat=a + 1) for eta in itertools.product(range(q), repeat=a)
               if not (Counter(eta) - Counter(xi)))
report("N_bal(a,3), a=1..5", [N_bal_formula(a, 3) for a in range(1, 6)], [3, 15, 93, 639, 4653])
report("N_bal(2,q), q=3,5,7,9,11", [N_bal_formula(2, q) for q in [3, 5, 7, 9, 11]], [15, 45, 91, 153, 231])
report("N_bal(4,5) = 7885 (§12.4)", N_bal_formula(4, 5), 7885)
report("N_ph(2,13) = N_bal(3,13) = 11713 (§12.4)", N_bal_formula(3, 13), 11713)
for (a, q) in [(1, 3), (2, 3), (3, 3), (1, 5), (2, 5)]:
    report(f"N_bal brute = formula at ({a},{q})", N_bal_brute(a, q), N_bal_formula(a, q))
    report(f"N_ph({a},{q}) brute = N_bal({a+1},{q})", N_ph_brute(a, q), N_bal_formula(a + 1, q))

# ---------- 4. ballot numbers ----------
exp_rows = {1: [2, 3, 1], 2: [5, 9, 5, 1], 3: [14, 28, 20, 7, 1], 4: [42, 90, 75, 35, 9, 1],
            5: [132, 297, 275, 154, 54, 11, 1], 6: [429, 1001, 1001, 637, 273, 77, 13, 1]}
for k, row in exp_rows.items():
    n1 = 2 * k + 1
    r1 = [math.comb(n1, k + j) - math.comb(n1, k + j + 2) for j in range(k + 2)]
    r2 = [Fraction(math.comb(2 * k + 2, k + 1 - j) * (2 * j + 1), (k + 2 + j)) for j in range(k + 2)]
    report(f"ballot row k={k}", r1, row)
    report(f"ballot closed form k={k}", [int(x) for x in r2], row)
    report(f"ballot row sum k={k} = Q_k(3)", sum(row), Qk(k, 3))

# ---------- 5. P_2(3) ----------
def matchings(idx):
    if not idx: yield []; return
    a = idx[0]
    for i in range(1, len(idx)):
        b = idx[i]; rest = idx[1:i] + idx[i+1:]
        for m in matchings(rest): yield [(a, b)] + m
def P_count(k, q):
    N = 2 * k + 2
    Js = list(matchings(list(range(N))))
    cnt = 0
    for x in itertools.product(range(q), repeat=N):
        if any(all((x[a] + x[b]) % q == 0 for (a, b) in J) for J in Js): cnt += 1
    return cnt
report("P_2(3) = 141 (§1.6)", P_count(2, 3), 141)
report("P_1(3)", P_count(1, 3), P_count(1, 3))  # printed only

# ---------- 6. Fact 9.2 |Gamma_K| = 4736 ----------
def gamma_K(k, m, K):
    # DS Definition 1.3, literal: a in mu_m^{n+1} (as exponents mod m), a_i != 1 (exp != 0), some J in K with a_{j_i} a_{k_i} = 1, i>=1
    n1 = 2 * k + 1
    cnt = 0
    for a in itertools.product(range(1, m), repeat=n1):
        aa = (None,) + a  # index 0 unused
        for J in K:
            if all((aa[j] + aa[kk]) % m == 0 for (j, kk) in J[1:]):
                cnt += 1; break
    return cnt
allJ = [sorted(J) for J in matchings(list(range(6)))]  # sorted: first pair contains 0
removed = [[(0, 1), (2, 3), (4, 5)], [(0, 2), (1, 5), (3, 4)]]
K13 = [J for J in allJ if J not in removed]
report("|J| at k=2", len(allJ), 15)
report("Fact 9.2 |Gamma_K| (13 matchings, m=9)", gamma_K(2, 9, K13), 4736)
report("Lemma 2.2 |Gamma_J| (15 matchings, m=9) = Q_2(9)", gamma_K(2, 9, allJ), 5120)

# ---------- 7. compatible colourings ----------
def compatible_colourings(k, r):
    n1 = 2 * k + 1
    cnt = 0
    for c in itertools.product(range(r), repeat=n1):  # exponents mod r
        c0 = (-sum(c)) % r
        full = [c0] + list(c)
        cl = Counter(full)
        if cl[0] % 2: continue
        if all(cl[z] == cl[(-z) % r] for z in range(1, r)): cnt += 1
    return cnt
report("compatible colourings (k,r)=(2,5)", compatible_colourings(2, 5), 1001)
report("compatible colourings (k,r)=(2,3)", compatible_colourings(2, 3), 141)
report("compatible colourings (k,r)=(2,7)", compatible_colourings(2, 7), 3301)
report("compatible colourings (k,r)=(1,5)", compatible_colourings(1, 5), 61)
report("compatible colourings (k,r)=(1,3)", compatible_colourings(1, 3), 19)

# ---------- 8. Lemma 10.4 ----------
def rep(a, m): return a % m
def delta(a):
    return tuple(2 * rep(t * a, 9) - 9 for t in (1, 2, 4))
report("delta(1)", delta(1), (-7, -5, -1)); report("delta(2)", delta(2), (-5, -1, 7))
report("delta(4)", delta(4), (-1, 7, 5)); report("delta(3)", delta(3), (-3, 3, -3))
signs = {a: tuple(1 if x > 0 else -1 for x in delta(a)) for a in range(1, 9)}
report("sign map bijective onto {±1}^3", len(set(signs.values())), 8)
M = [[4, 2, 1], [-1, 4, 2], [-2, -1, 4]]
def matvec(M, v): return tuple(sum(M[i][j] * v[j] for j in range(3)) for i in range(3))
report("delta = M s for all a", all(matvec(M, signs[a]) == delta(a) for a in range(1, 9)), True)
detM = (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0]) + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
report("det M", detM, 81)
def hodge_count(k, m):
    N = 2 * k + 2
    units = [t for t in range(1, m) if math.gcd(t, m) == 1]
    B = 0; D = 0
    for a in itertools.product(range(1, m), repeat=N - 1):
        a0 = (-sum(a)) % m
        if a0 == 0: continue
        full = (a0,) + a
        if all(sum(rep(t * x, m) for x in full) == m * (k + 1) for t in units):
            B += 1
            c = Counter(full)
            if all(c[x] == c[(-x) % m] for x in c): D += 1
    return B, D
for k in (1, 2):
    B, D = hodge_count(k, 9)
    report(f"|B| at (k,m)=({k},9) = C(N,N/2)^3", B, math.comb(2*k+2, k+1) ** 3)
    report(f"|D| at (k,m)=({k},9) = Q_k(9)", D, Qk(k, 9))
for m in (5, 7, 15):
    B, D = hodge_count(1, m)
    print(f"  (k,m)=(1,{m}): |B|={B} |D|={D} Q_1={Qk(1,m)}")
    report(f"|D| = Q_1({m})", D, Qk(1, m))
    if m in (5, 7): report(f"|B| = |D| at prime m={m} (H4)", B, D)

# ---------- 9. Corollary W(ii): Gamma_K for K = J(1,2) ----------
K12 = [J for J in allJ if (4, 5) in J]
report("|J(1,2)| = 3", len(K12), 3)
for m in (5, 9):
    report(f"|Gamma_K| K=J(1,2), m={m} = Q_1(m)(m-1)", gamma_K(2, m, K12), Qk(1, m) * (m - 1))

# ---------- 10. Lemma 6.8 at k=1 ----------
def N_bal_q(a, q): return N_bal_formula(a, q)
def lemma68(k, m, q, r):
    n1 = 2 * k + 1
    tot = 0
    for c in itertools.product(range(r), repeat=n1):
        c0 = (-sum(c)) % r
        full = [c0] + list(c)
        cl = Counter(full)
        if cl[0] % 2: continue
        if not all(cl[z] == cl[(-z) % r] for z in range(1, r)): continue
        # block of colour 1
        s1 = cl[0]
        prod = Qk(s1 // 2 - 1, q) if s1 >= 2 else 1  # N_1(c): closed s1-tuples = Q_{s1/2-1}(q); s1=0 -> 1
        for z in range(1, (r + 1) // 2):
            A = [i for i in range(n1 + 1) if full[i] == z]; Bb = [i for i in range(n1 + 1) if full[i] == r - z]
            al = len([i for i in A if i != 0]); be = len([i for i in Bb if i != 0])
            if 0 in A or 0 in Bb: prod *= N_bal_q(min(al, be) + 1, q)  # N_ph(a) = N_bal(a+1)
            else: prod *= N_bal_q(al, q)
        tot += prod
    return tot
Js1 = [sorted(J) for J in matchings(list(range(4)))]
for (m, q, r) in [(15, 3, 5), (15, 5, 3), (21, 3, 7), (21, 7, 3)]:
    report(f"Lemma 6.8 k=1 m={m} (q={q},r={r}) sum of block counts = |Gamma_J| = Q_1({m})", lemma68(1, m, q, r), Qk(1, m))
    report(f"literal |Gamma_J| k=1 m={m}", gamma_K(1, m, Js1), Qk(1, m))

print("ALL AGREE" if ok_all else "SOME DISAGREE")
