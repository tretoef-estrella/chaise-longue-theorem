#!/usr/bin/env python3
"""STEP 5 — independent numerical sanity checks of the Lean statement, written from the Lean
definitions (NOT from the authors' scripts).
(a) TheoremB.Qk exactly as in Lean (Fin((q-1)/2) -> range(2k+3), filter 2*sum = 2k+2, N!/prod(b!)^2
    with floor division); check every summand divides exactly; compare with the paper's table (§3),
    the polynomials Q_1, Q_2, Q_3 of §3, Q_k(3) = C(2k+2,k+1), and the values in TheoremB/Checks.lean.
(b) |Gamma_J| of [DS, Def. 1.3] by brute force over exponent vectors, compare with Qk.
(c) Qk k m < m^(2k+1) for odd m <= 99, k <= 8 (no truncation in the Lean subtraction, rank >= 1).
(d) The Z-module R/(psi_J) built from the Lean formula of psiP: rank over F_p for several p and over a
    large prime (proxy for Q), and the elementary divisors over Z (Smith form) in the smallest cells;
    expected: dim of ideal = Qk k m over every p, elementary divisors all 1, quotient rank m^(2k+1)-Qk.
(e) Negative controls: two deliberately wrong psi_J; expected: the equality fails in at least one cell.
Expected output: 'ALL OK' at the end; controls phi_plus and tau_plus fail in some cell; wrongend
(added in run 3 as an equivalence check, see note in (e)) fails in no cell. Time estimate: < 2 min, < 300 MB.
"""
import itertools, math, sys, time
import numpy as np
from math import factorial, comb

def Qk(k, q):  # literal transcription of TheoremB.Qk
    h = (q - 1) // 2; N = 2 * k + 2; tot = 0
    for b in itertools.product(range(2 * k + 3), repeat=h):
        if 2 * sum(b) == N:
            den = 1
            for x in b: den *= factorial(x) ** 2
            assert factorial(N) % den == 0, ('inexact division', k, q, b)
            tot += factorial(N) // den
    return tot


from fractions import Fraction
def Qgf(k, q):  # N! [x^N] I_0(2x)^h, exact rational arithmetic (the paper's formula, §1.2)
    h = (q - 1) // 2; N = 2 * k + 2
    term = [Fraction(1, factorial(e // 2) ** 2) if e % 2 == 0 else Fraction(0) for e in range(N + 1)]
    poly = [Fraction(1)] + [Fraction(0)] * N
    for _ in range(h):
        poly = [sum(poly[i] * term[e - i] for i in range(e + 1)) for e in range(N + 1)]
    return int(poly[N] * factorial(N))

def Q(k, q):  # literal Lean sum when cheap, else the generating function
    return Qk(k, q) if (q - 1) // 2 <= 6 else Qgf(k, q)

ok = True
def check(cond, msg):
    global ok
    print(('  ok   ' if cond else '  FAIL ') + msg)
    ok = ok and cond

print('(a) Qk against the paper')
table = {3: [6, 20, 70, 252, 924], 5: [36, 400, 4900, 63504, 853776], 7: [90, 1860, 44730, 1172556, 32496156],
         9: [168, 5120, 190120, 7939008, 357713664], 11: [270, 10900, 551950, 32232060, 2070891900],
         13: [396, 19920, 1281420, 96807312, 8175770064]}
for q, row in table.items():
    got = [Qk(k, q) for k in range(1, 6)]
    check(got == row, f'table row q={q}: {got}')
for q in (25, 27):
    print('   q=%d via generating function:' % q, [Qgf(k, q) for k in range(1, 6)])
for q in range(3, 14, 2):
    for k in range(0, 5):
        assert Qk(k, q) == Qgf(k, q), (k, q)
print('   literal Lean sum == generating function for odd q in 3..13, k in 0..4')
for q in range(3, 40, 2):
    assert Q(0, q) == q - 1 and Q(1, q) == 3 * (q - 1) * (q - 2) and Q(2, q) == 15*q**3 - 90*q**2 + 175*q - 100 \
        and Q(3, q) == 105*q**4 - 1050*q**3 + 3955*q**2 - 6335*q + 3325, q
print('   polynomials Q_0..Q_3 of §3 hold for all odd q in 3..39')
check(all(Qk(k, 3) == comb(2 * k + 2, k + 1) for k in range(9)), 'Q_k(3) = C(2k+2,k+1), k<=8')
check([Qk(k, 1) for k in range(6)] == [0] * 6, 'Q_k(1) = 0 (m = 1)')
check((Qk(0, 3), Qk(0, 5), Qk(1, 3), Qk(1, 5), Qk(1, 7), Qk(1, 9), Qk(2, 3), Qk(2, 5), Qk(3, 3)) == (2, 4, 6, 36, 90, 168, 20, 400, 70), 'values of TheoremB/Checks.lean')

def matchings(n):  # fixed-point-free involutions of range(n), as list J
    if n == 0: yield []; return
    def rec(free, J):
        if not free: yield list(J); return
        a = free[0]
        for b in free[1:]:
            J[a], J[b] = b, a
            yield from rec([x for x in free if x not in (a, b)], J)
    yield from rec(list(range(n)), [None] * n)

print('(b) |Gamma_J| of [DS, Def. 1.3] by brute force')
for m, k in [(3, 0), (5, 0), (3, 1), (5, 1), (7, 1), (9, 1), (15, 1), (3, 2), (5, 2), (9, 2), (3, 3)]:
    d = 2 * k + 1; Js = list(matchings(2 * k + 2))
    pairs = [[(a, J[a]) for a in range(2 * k + 2) if a < J[a] and a > 0] for J in Js]
    cnt = 0
    for e in itertools.product(range(1, m), repeat=d):  # a_i != 1  <=>  e_i != 0
        ee = (None,) + e
        if any(all((ee[a] + ee[b]) % m == 0 for a, b in P) for P in pairs): cnt += 1
    check(cnt == Qk(k, m), f'(m,k)=({m},{k}): |Gamma_J| = {cnt}, Qk = {Qk(k, m)}, |J| = {len(Js)}')

print('(c) no truncation: Qk k m < m^(2k+1)')
worst = None
for m in range(1, 100, 2):
    for k in range(0, 9):
        q = Q(k, m) if m > 1 else Qk(k, m)
        if not q < m ** (2 * k + 1): check(False, f'Qk >= m^(2k+1) at (m,k)=({m},{k})')
        if q > (m - 1) ** (2 * k + 1) and m > 1: check(False, f'Qk > (m-1)^(2k+1) at ({m},{k})')
print('   checked Qk <= (m-1)^(2k+1) < m^(2k+1) for odd m<100, k<=8')

# ---- (d) the module R/(psi_J) from the Lean formula -----------------------------------------
def psi_poly(m, k, J, variant='lean'):
    """psiP m J as dict {exponent tuple (mod m) over t_1..t_d: integer coeff}; tP 0 = 0 never used."""
    d = 2 * k + 1
    def var(a):  # t_a, a>=1 -> monomial
        e = [0] * d; e[a - 1] = 1; return {tuple(e): 1}
    def mul(P, Q):
        R = {}
        for e1, c1 in P.items():
            for e2, c2 in Q.items():
                e = tuple((x + y) % m for x, y in zip(e1, e2)); R[e] = R.get(e, 0) + c1 * c2
        return {e: c for e, c in R.items() if c}
    one = {tuple([0] * d): 1}
    def add(P, Q, s=1):
        R = dict(P)
        for e, c in Q.items(): R[e] = R.get(e, 0) + s * c
        return {e: c for e, c in R.items() if c}
    def phi(u):
        R, pw = {}, one
        for s in range(m): R = add(R, pw); pw = mul(pw, u)
        return R
    P = one
    for a in range(2 * k + 2):
        b = J[a]
        if a < b:
            big = b if variant != 'wrongend' or a == 0 else a  # control: (t_{j_i}-1) instead of (t_{k_i}-1) for i>=1
            P = mul(P, add(var(big), one, -1 if variant != 'tau_plus' else 1))  # control tau_plus: t+1 for t-1
            if a > 0:
                u = mul(var(a), var(b))
                f = phi(u) if variant != 'phi_plus' else add(u, one, 1)  # control: phi replaced by u+1
                P = mul(P, f)
    return P

def ideal_matrix(m, k, variant='lean'):
    d = 2 * k + 1; n = m ** d
    idx = {e: i for i, e in enumerate(itertools.product(range(m), repeat=d))}
    rows = []
    for J in matchings(2 * k + 2):
        P = psi_poly(m, k, J, variant)
        for g in idx:  # the ideal of a group ring is the Z-span of the translates g*psi_J
            r = np.zeros(n, dtype=np.int64)
            for e, c in P.items():
                r[idx[tuple((x + y) % m for x, y in zip(e, g))]] += c
            rows.append(r)
    return np.array(rows, dtype=np.int64), n

def rank_mod_p(A, p):
    M = np.mod(A, p).astype(np.int64); r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = np.nonzero(M[r:, c])[0]
        if piv.size == 0: continue
        i = r + piv[0]
        if i != r: M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        nz = np.nonzero(M[:, c])[0]; nz = nz[nz != r]
        if nz.size:
            M[nz] = (M[nz] - np.outer(M[nz, c], M[r]) % p) % p
        r += 1
        if r == rows: break
    return r

def elementary_divisors(A):
    """Smith normal form diagonal of an integer matrix (python ints), small sizes only."""
    M = [list(map(int, row)) for row in A if any(row)]
    divs = []
    while M and any(any(x for x in row) for row in M):
        # pick the entry of smallest absolute value
        best = None
        for i, row in enumerate(M):
            for j, x in enumerate(row):
                if x and (best is None or abs(x) < best[0]): best = (abs(x), i, j)
        _, i, j = best
        M[0], M[i] = M[i], M[0]
        for row in M: row[0], row[j] = row[j], row[0]
        while True:
            p = M[0][0]; changed = False
            for i in range(1, len(M)):
                if M[i][0]:
                    qt = M[i][0] // p; M[i] = [a - qt * b for a, b in zip(M[i], M[0])]
                    if M[i][0]: changed = True
            for j in range(1, len(M[0])):
                if M[0][j]:
                    qt = M[0][j] // p
                    for row in M: row[j] -= qt * row[0]
                    if M[0][j]: changed = True
            if not changed: break
            best = None
            for i in range(len(M)):
                if M[i][0] and (best is None or abs(M[i][0]) < best[0]): best = (abs(M[i][0]), i, 'r')
            for j in range(len(M[0])):
                if M[0][j] and (best is None or abs(M[0][j]) < best[0]): best = (abs(M[0][j]), j, 'c')
            if best[2] == 'r': M[0], M[best[1]] = M[best[1]], M[0]
            else:
                for row in M: row[0], row[best[1]] = row[best[1]], row[0]
        p = abs(M[0][0])
        rest = [row[1:] for row in M[1:] if any(row[1:])]
        if any(x % p for row in rest for x in row):  # enforce divisibility chain
            M = [[p] + [0] * (len(M[0]) - 1)] + [row for row in M[1:]]
            for j in range(1, len(M[0])):
                for i in range(1, len(M)):
                    if M[i][j] % p: M[0][j] = 0; M[0] = [a + b for a, b in zip(M[0], M[i])]; break
                else: continue
                break
            continue
        divs.append(p); M = rest
    return divs

print('(d) R/(psi_J) from the Lean formula')
BIGP = 2147483629  # a prime < 2^31
cells = [(1, 0), (1, 1), (1, 2), (3, 0), (5, 0), (7, 0), (3, 1), (5, 1), (7, 1), (9, 1), (3, 2)]
for m, k in cells:
    t0 = time.time(); A, n = ideal_matrix(m, k); q = Qk(k, m)
    rk = {p: rank_mod_p(A, p) for p in (2, 3, 5, 7, 11, 13, BIGP)}
    check(all(v == q for v in rk.values()), f'(m,k)=({m},{k}) n={n} rows={A.shape[0]}: dim_Fp ideal = {rk} vs Qk={q}; dim quotient = {n - q}  [{time.time()-t0:.1f}s]')
    if n <= 343:
        t0 = time.time(); ed = elementary_divisors(A)
        check(len(ed) == q and all(x == 1 for x in ed), f'   Smith form over Z: {len(ed)} elementary divisors, all 1: {all(x == 1 for x in ed)} -> Z^n/L free of rank {n - len(ed)}  [{time.time()-t0:.1f}s]')

print('(e) negative controls (expected to FAIL the equality somewhere)')
# NOTE (run 2): 'wrongend' is NOT a valid control: in R, u*phi(u) = phi(u) for u = t_j t_k, so
# (t_j - 1) phi = (t_k^{-1} - 1) phi = -t_k^{-1} (t_k - 1) phi, a unit multiple of the true factor.
# It is kept as an EQUIVALENCE check (expected: 0 failing cells); the real controls are phi_plus, tau_plus.
for variant in ('wrongend', 'phi_plus', 'tau_plus'):
    bad = []
    for m, k in [(3, 1), (5, 1), (7, 1), (3, 2)]:
        A, n = ideal_matrix(m, k, variant); q = Qk(k, m)
        rk = {p: rank_mod_p(A, p) for p in (2, 3, 5, 7, BIGP)}
        if any(v != q for v in rk.values()): bad.append(((m, k), rk, q))
    print(f'   control {variant}: cells where equality fails: {len(bad)}', bad[:3])
    ok = ok and ((len(bad) == 0) if variant == 'wrongend' else (len(bad) > 0))
print('ALL OK' if ok else 'SOME CHECK FAILED')
