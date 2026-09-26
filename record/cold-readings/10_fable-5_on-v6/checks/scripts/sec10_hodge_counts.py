#!/usr/bin/env python3
"""
sec10_hodge_counts.py -- independent recount of the Hodge-character sets of §10
(PAPER_OFICIAL_v6.md, lines 699-732), written from Aoki's definitions (p. 23):

  A = { (a_0..a_{N-1}) in {1..m-1}^N : sum a_i = 0 mod m },  N = 2k+2
  B = { alpha in A : sum_i <t a_i> = m(k+1) for every unit t mod m }   (Hodge characters)
  D = { alpha in A : multiset splits into pairs {a, m-a} }               (pair type)

Everything is counted as ORDERED tuples (as in Aoki and in the paper), by
enumerating multisets and weighting by the multinomial coefficient.
Also checks:  |A| = ((m-1)^N + (-1)^N (m-1))/m  (dim of primitive cohomology),
              D subset of B (Lemma 10.1(i)),  |D| = Q_k(m) (Lemma 10.1(ii)),
              Lemma 10.4 (delta table, sign bijection, M, det M = 81, C(N,N/2)^3),
              (H4) numerics: B_{1,chi} != 0 for all odd characters of odd primes p < 200,
              the (n+2)! / (n+1)! / "prime factor >= 2k+3" equivalence.

PREDICTIONS (paper, Remark 10.3 / Lemma 10.4 / §12):
  |B| - Q_k(m) = 48 (1,9), 2880 (2,9), 152880 (3,9), 8064000 (4,9);
  192 (1,27); 288 (1,15); 432 (1,21); 528 (1,45); 45360 (2,15); 0 at (1,25),(1,35).
  |B| = 216, 8000, 343000, 16003008 at m=9, k=1..4.
  Prime cells: |B| = Q_k(m).
Cost prediction: largest cell here is (2,15): C(19,6)=27132 multisets; (4,9): C(17,10)=19448;
(3,11): C(17,8)=24310.  Total < 15 s, < 60 MB.
"""
import sys, time, itertools, math, cmath
from math import comb, factorial, gcd
from fractions import Fraction
import numpy as np

T0 = time.time()

def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]

def Q_formula(k, m):
    """Q_k(m) = N! [x^N] I_0(2x)^h, h=(m-1)/2, exact rational arithmetic."""
    N = 2 * k + 2
    h = (m - 1) // 2
    c = [Fraction(0)] * (N + 1)
    for b in range(N // 2 + 1):
        c[2 * b] = Fraction(1, factorial(b) ** 2)
    P = [Fraction(0)] * (N + 1)
    P[0] = Fraction(1)
    for _ in range(h):
        newP = [Fraction(0)] * (N + 1)
        for i, pi in enumerate(P):
            if pi == 0:
                continue
            for j in range(0, N + 1 - i, 2):
                newP[i + j] += pi * c[j]
        P = newP
    v = P[N] * factorial(N)
    assert v.denominator == 1
    return int(v)

def count_cell(k, m, chunk=200000, all_units=True):
    """Return dict with |A|, |B|, |D| (ordered tuples), and consistency flags."""
    N = 2 * k + 2
    U = units(m)
    if not all_units:
        # one representative per {t,-t}: enough because <-x> = m - <x> for x != 0
        U = [t for t in U if t <= m // 2]
    target = m * (k + 1)
    Nfact = factorial(N)
    tot_A = 0
    tot_B = 0
    tot_D = 0
    pair_not_hodge = 0
    hodge_multisets = 0
    it = itertools.combinations_with_replacement(range(1, m), N)
    half = m / 2.0
    while True:
        block = list(itertools.islice(it, chunk))
        if not block:
            break
        A = np.array(block, dtype=np.int32)          # rows sorted nondecreasing
        rows = A.shape[0]
        # multinomial weights: N! / prod(run lengths!)  (= N! / prod over positions of run index)
        runidx = np.ones((rows, N), dtype=np.int64)
        for j in range(1, N):
            eq = A[:, j] == A[:, j - 1]
            runidx[:, j] = np.where(eq, runidx[:, j - 1] + 1, 1)
        denom = np.prod(runidx, axis=1)
        w = Nfact // denom                              # exact (denom | N!)
        assert np.all(w * denom == Nfact)
        # A: sum = 0 mod m
        inA = (A.sum(axis=1) % m) == 0
        # B: Hodge condition for every unit t
        hodge = np.ones(rows, dtype=bool)
        for t in U:
            S = ((t * A) % m).sum(axis=1)
            hodge &= (S == target)
        # D: pair type: for each class c=min(a,m-a), #a<m/2 equals #a>m/2
        h = (m - 1) // 2
        if m % 2 == 1:
            cls = np.minimum(A, m - A) - 1                # 0..h-1
            sgn = np.where(A < half, 1, -1).astype(np.int64)
            flat = (np.arange(rows)[:, None] * h + cls).ravel()
            D = np.bincount(flat, weights=sgn.ravel(), minlength=rows * h).reshape(rows, h)
            pair = np.all(D == 0, axis=1)
        else:
            pair = np.zeros(rows, dtype=bool)         # not used for even m
        tot_A += int(w[inA].sum())
        tot_B += int(w[hodge].sum())
        tot_D += int(w[pair].sum())
        pair_not_hodge += int(np.sum(pair & ~hodge))
        hodge_multisets += int(hodge.sum())
        # Hodge => in A (sanity)
        assert np.all(inA[hodge]), "Hodge tuple with sum != 0 ??"
    return dict(N=N, A=tot_A, B=tot_B, D=tot_D, pair_not_hodge=pair_not_hodge,
                hodge_multisets=hodge_multisets)

def report(k, m, expected_diff=None, note=""):
    t = time.time()
    r = count_cell(k, m)
    N = r['N']
    A_formula = ((m - 1) ** N + (-1) ** N * (m - 1)) // m
    Q = Q_formula(k, m) if m % 2 == 1 else None
    diff = r['B'] - (Q if Q is not None else 0)
    line = (f"(k,m)=({k},{m}) N={N}: |A|={r['A']} (formula {A_formula}) "
            f"|B|={r['B']} |D|={r['D']} Q_k(m)={Q} |B|-Q={diff} "
            f"pair_not_hodge={r['pair_not_hodge']} [{time.time()-t:.1f}s]")
    flags = []
    if r['A'] != A_formula: flags.append("A-MISMATCH")
    if m % 2 == 1 and r['D'] != Q: flags.append("D!=Q")
    if r['pair_not_hodge']: flags.append("PAIR-NOT-HODGE")
    if expected_diff is not None and diff != expected_diff:
        flags.append(f"PAPER SAYS {expected_diff}: MISMATCH")
    elif expected_diff is not None:
        flags.append(f"paper says {expected_diff}: OK")
    print(line, " ".join(flags), note)
    sys.stdout.flush()
    return r

print("=== Remark 10.3 / mandated cells ===")
report(1, 9, 48)
report(2, 9, 2880)
report(3, 9, 152880)
report(4, 9, 8064000, note="Lemma 10.4 k=4")
report(1, 27, 192)
report(1, 15, 288)
report(1, 21, 432)
report(1, 45, 528)
report(2, 15, 45360)
report(1, 25, 0)
report(1, 35, 0)

print("\n=== Prime cells (§12: |B| = Q_k(m)) ===")
for (k, m) in [(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(2,11),(3,3),(3,5),(4,3),(3,7),(3,11),(2,13)]:
    report(k, m, 0)

print("\n=== Lemma 10.4 (m = 9) ===")
m = 9
rep = lambda x: x % 9
delta = {a: (2*rep(a)-9, 2*rep(2*a)-9, 2*rep(4*a)-9) for a in range(1, 9)}
for a in range(1, 9):
    print(f"  delta({a}) = {delta[a]}")
print("  paper: delta(1)=(-7,-5,-1) delta(2)=(-5,-1,7) delta(4)=(-1,7,5) delta(3)=(-3,3,-3):",
      delta[1] == (-7,-5,-1) and delta[2] == (-5,-1,7) and delta[4] == (-1,7,5) and delta[3] == (-3,3,-3))
print("  delta(-a) = -delta(a) for all a:", all(tuple(-x for x in delta[a]) == delta[9-a] for a in range(1,9)))
signs = {a: tuple(1 if x > 0 else -1 for x in delta[a]) for a in range(1, 9)}
print("  no zero coordinate:", all(0 not in delta[a] for a in range(1,9)))
print("  sign map is a bijection onto {+-1}^3:", len(set(signs.values())) == 8)
M = np.array([[4, 2, 1], [-1, 4, 2], [-2, -1, 4]])
print("  det M =", round(np.linalg.det(M)), " (paper: 81)")
print("  delta(a) = M s(a) for all a:", all(tuple(M @ np.array(signs[a])) == delta[a] for a in range(1,9)))
# closed form vs direct counts
for k in range(1, 6):
    N = 2*k+2
    cf = comb(N, N//2) ** 3
    Q = Q_formula(k, 9)
    print(f"  k={k}: C({N},{N//2})^3 = {cf}, Q_k(9) = {Q}, difference = {cf - Q}")
# direct check of the reformulation: Hodge <=> balanced signs, over all tuples for k=1,2 (ordered, brute force)
for k in (1, 2):
    N = 2*k+2
    U = units(9)
    cnt_hodge = 0; cnt_bal = 0; agree = True
    for tup in itertools.product(range(1, 9), repeat=N):
        hodge = all(sum((t*a) % 9 for a in tup) == 9*(k+1) for t in U)
        bal = all(sum(signs[a][c] for a in tup) == 0 for c in range(3))
        cnt_hodge += hodge; cnt_bal += bal
        if hodge != bal: agree = False
    print(f"  brute force k={k}: #Hodge (ordered) = {cnt_hodge}, #balanced = {cnt_bal}, pointwise equal: {agree}")

print("\n=== (H4) numerics: B_{1,chi} for odd characters of odd primes p < 200 ===")
def primes_below(n):
    return [p for p in range(2, n) if all(p % d for d in range(2, int(p**0.5)+1))]
def primitive_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in set(f for f in range(2, p) if (p-1) % f == 0 and all(f % d for d in range(2, int(f**0.5)+1)))):
            return g
    return 1
total_odd = 0; nonzero = 0; minabs = 1e9
for p in primes_below(200):
    if p == 2: continue
    g = primitive_root(p)
    log = {}
    x = 1
    for e in range(p-1):
        log[x] = e; x = (x*g) % p
    for j in range(p-1):
        chi = lambda a, j=j: cmath.exp(2j*cmath.pi*1j*log[a]/(p-1)) if False else cmath.exp(2*cmath.pi*1j*j*log[a]/(p-1))
        if abs(chi(p-1) + 1) > 1e-9:   # need chi(-1) = -1
            continue
        total_odd += 1
        B1 = sum(chi(u) * u for u in range(1, p)) / p
        if abs(B1) > 1e-9:
            nonzero += 1
        minabs = min(minabs, abs(B1))
print(f"  odd characters counted: {total_odd} (paper: 2090); with B_1,chi != 0: {nonzero}; min |B_1,chi| = {minabs:.4f}")
print("  p=3: B_{1,Legendre} =", (1*1 + (-1)*2)/3)

print("\n=== conversions of Aoki's condition (odd m <= 999, k <= 12) ===")
ok = True
for k in range(1, 13):
    n = 2*k
    for m in range(3, 1000, 2):
        pf = [p for p in range(2, m+1) if m % p == 0 and all(p % d for d in range(2, int(p**0.5)+1))]
        c1 = all(p > n + 2 for p in pf)
        c2 = all(p >= 2*k + 3 for p in pf)
        c3 = gcd(m, factorial(n+2)) == 1
        c4 = gcd(m, factorial(n+1)) == 1
        if not (c1 == c2 == c3 == c4):
            ok = False; print("  MISMATCH", k, m, c1, c2, c3, c4)
print("  all four formulations agree for odd m:", ok)

print(f"\nTOTAL TIME {time.time()-T0:.1f}s")
