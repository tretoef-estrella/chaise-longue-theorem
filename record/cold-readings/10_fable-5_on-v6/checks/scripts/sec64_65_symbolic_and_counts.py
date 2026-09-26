#!/usr/bin/env python3
"""
Referee check for PAPER_OFICIAL_v6.md, §6.4–§6.5 (Lemma 6.6, Lemma 6.7).

Part A (sympy, symbolic, characteristic-free identities):
  Lemma 6.7(i):  z = (1+eps)^{-1} - 1 == -eps (1+eps)^{-1}.
  Lemma 6.7(ii): with t_i = zeta(1+x), t_l = zeta^{-1}(1+z)^{-1}:
                 t_i t_l - 1 == (x - z)(1+z)^{-1}.
  Lemma 2.3(ii): y_j + y_k == (t_j + t_k)(t_j t_k)^{-1}(t_j t_k - 1), y = t - t^{-1}.
Part B (polynomial identities mod p, used at line 500 through Lemma 2.4(i)):
  (a+b)^{q-1} b == -a b D(a,b)  in F_p[a,b]/(b^q), for q = 3,5,7,9,25,27.
  D(a,b) == (b^{q-1} - a^{q-1})/(a+b) over Z.
Part C (counting, brute force):
  N_1(c) as defined at line 504, for 0 in C_1 and 0 not in C_1, |C_1| = 2k',
  compared with Q_{k'-1}(q) = (2k')! [x^{2k'}] I_0(2x)^h and with the
  number of 2k'-tuples in T closed under u -> -u (|Z_{{emptyset}}|).
  Also: the parenthetical "w_0 != 1 is automatic for |C_1| even".
"""
import itertools, math, sys, time
from fractions import Fraction
import sympy as sp

t0 = time.time()
ok_all = True
def report(name, ok):
    global ok_all
    ok_all &= bool(ok)
    print(f"[{'OK' if ok else 'FAIL'}] {name}")

# ---------------- Part A: symbolic identities ----------------
x, z, eps, zeta, tj, tk = sp.symbols('x z epsilon zeta t_j t_k')

# Lemma 6.7(i)
lhs = 1/(1+eps) - 1
rhs = -eps/(1+eps)
report("Lemma 6.7(i): (1+eps)^{-1} - 1 == -eps(1+eps)^{-1}", sp.simplify(lhs - rhs) == 0)

# Lemma 6.7(ii)
ti = zeta*(1+x)
tl = (1+z)**-1 / zeta
lhs = ti*tl - 1
rhs = (x - z)/(1+z)
report("Lemma 6.7(ii): t_i t_l - 1 == (x - z)(1+z)^{-1}", sp.simplify(lhs - rhs) == 0)
# and the inverse change of variables is consistent with the definitions
xi_def = ti/zeta - 1
zl_def = 1/(zeta*tl) - 1
report("Lemma 6.7 defs: x = zeta^{-1} t_i - 1, z = (zeta t_l)^{-1} - 1 recover x,z",
       sp.simplify(xi_def - x) == 0 and sp.simplify(zl_def - z) == 0)

# Lemma 2.3(ii)
yj = tj - 1/tj; yk = tk - 1/tk
report("Lemma 2.3(ii): y_j + y_k == (t_j+t_k)(t_j t_k)^{-1}(t_j t_k - 1)",
       sp.simplify(yj + yk - (tj+tk)/(tj*tk)*(tj*tk-1)) == 0)

# ---------------- Part B: identities mod p ----------------
a, b = sp.symbols('a b')
def D(q):
    return sum((-1)**u * a**u * b**(q-2-u) for u in range(q-1))
for q in [3, 5, 7, 9, 25, 27]:
    # (b^{q-1} - a^{q-1})/(a+b) == D over Z (q-2 odd)
    quo, rem = sp.div(sp.Poly(b**(q-1) - a**(q-1), a, b), sp.Poly(a+b, a, b))
    report(f"D formula q={q}: (b^(q-1)-a^(q-1))/(a+b) == D, remainder 0",
           rem.is_zero and sp.expand(quo.as_expr() - D(q)) == 0)
    p = sp.factorint(q); p = list(p.keys())[0]
    # (a+b)^{q-1} b + a b D(a,b) == 0 in F_p[a,b]/(b^q)
    e = sp.Poly(sp.expand((a+b)**(q-1)*b + a*b*D(q)), a, b, modulus=p)
    # drop terms with b-degree >= q
    bad = [m for m in e.monoms() if m[1] < q]
    report(f"Lemma 2.4(i) q={q} p={p}: (a+b)^(q-1) b == -a b D(a,b) mod (b^q)", len(bad) == 0)

# ---------------- Part C: counts ----------------
def Q(k, q):
    """Q_k(q) = N! [x^N] I_0(2x)^h, N = 2k+2, h=(q-1)/2, exact."""
    N = 2*k+2; h = (q-1)//2; n = N//2
    tot = Fraction(0)
    # coefficient of x^{2n} in (sum_b x^{2b}/(b!)^2)^h : compositions of n into h parts
    def rec(i, rem):
        if i == h-1:
            return Fraction(1, math.factorial(rem)**2)
        s = Fraction(0)
        for bb in range(rem+1):
            s += Fraction(1, math.factorial(bb)**2) * rec(i+1, rem-bb)
        return s
    if h == 0:
        return 1 if N == 0 else 0
    tot = rec(0, n)
    val = tot * math.factorial(N)
    assert val.denominator == 1
    return int(val)

def closed_under_inversion(ms, q):
    """ms: list of exponents in Z/q (values w = zeta_q^e). Closed under inversion
    iff multiplicity of e equals multiplicity of -e for all e."""
    from collections import Counter
    c = Counter(e % q for e in ms)
    return all(c[e] == c[(-e) % q] for e in c)

def N1_count(q, size, zero_in):
    """N_1(c) per line 504. size = |C_1| = 2k' (or odd). If zero_in: tuples
    indexed by C_1 \\ {0} (size-1 entries) in mu_q \\ {1}, w_0 = (prod)^{-1};
    require the full multiset to lie in mu_q\\{1} and be closed under inversion."""
    nz = list(range(1, q))
    n = size - 1 if zero_in else size
    cnt = 0
    cnt_w0_is_1 = 0
    for tup in itertools.product(nz, repeat=n):
        ms = list(tup)
        if zero_in:
            w0 = (-sum(tup)) % q
            if w0 == 0:
                # w_0 = 1: check whether the rest is nevertheless closed
                if closed_under_inversion(ms, q):
                    cnt_w0_is_1 += 1
                continue
            ms.append(w0)
        if closed_under_inversion(ms, q):
            cnt += 1
    return cnt, cnt_w0_is_1

for q in [3, 5, 7, 9]:
    for size in [0, 1, 2, 3, 4, 5, 6]:
        if q**size > 2_000_000:
            continue
        c_out, _ = N1_count(q, size, zero_in=False)
        c_in, bad_in = N1_count(q, size, zero_in=True) if size >= 1 else (0, 0)
        if size % 2 == 0:
            kp = size // 2
            expect = Q(kp-1, q) if kp >= 1 else 1
            report(f"N_1 q={q} |C_1|={size} (0 not in C_1): {c_out} == Q_{kp-1}(q)={expect}", c_out == expect)
            if size >= 1:
                report(f"N_1 q={q} |C_1|={size} (0 in C_1):     {c_in} == Q_{kp-1}(q)={expect}", c_in == expect)
                report(f"   parenthetical: no closed tuple with w_0 = 1 when |C_1| even (found {bad_in})", bad_in == 0)
        else:
            report(f"N_1 q={q} |C_1|={size} odd: both counts 0 (got {c_out}, {c_in})", c_out == 0 and c_in == 0)

# |Z_{{emptyset}}| for T = a set with fixed-point-free involution: same count as
# 2k'-tuples closed under inversion (bijection mu_q\{1} -> T). Check a table of Q values
# against the paper's table (§3) at k=1..3.
table = {3: [6, 20, 70], 5: [36, 400, 4900], 7: [90, 1860, 44730], 9: [168, 5120, 190120],
         11: [270, 10900, 551950], 13: [396, 19920, 1281420], 25: [1656, 182400, 26926200],
         27: [1950, 234260, 37849630]}
for q, vals in table.items():
    got = [Q(k, q) for k in (1, 2, 3)]
    report(f"Q_k({q}) k=1..3 == paper's table {vals}", got == vals)
    report(f"Q_0({q}) == q-1", Q(0, q) == q-1)

print(f"\nALL OK: {ok_all}   elapsed {time.time()-t0:.1f}s")
sys.exit(0 if ok_all else 1)
