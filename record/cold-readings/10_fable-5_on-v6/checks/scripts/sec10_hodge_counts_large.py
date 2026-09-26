#!/usr/bin/env python3
"""
sec10_hodge_counts_large.py -- the remaining cells of Remark 10.3 and §12 (Hodge characters),
with a SECOND, independent enumeration for k = 1 (ordered tuples (a0,a1,a2), a3 determined),
cross-checked against the multiset method on cells already counted in sec10_hodge_counts.py.

Definitions as in sec10_hodge_counts.py (Aoki p. 23): A, B (Hodge), D (pair type), N = 2k+2.

PREDICTIONS (paper, Remark 10.3 / §12):
  |B| - Q_1(81) = 624;  |B| - Q_2(25) = 2880;  |B| - Q_2(35) = 4320;
  |B| - Q_1(m) = 0 for m = 49, 55, 77, 121 (and 25, 35 again by the ordered method).
  Cross-check (must equal first script): (1,9): 216/168; (1,15): 834/546; (1,45): 6204/5676; (1,27): 2142/1950.
Even m, k = 1 (code sanity only, outside the paper's scope): 1 + |B| should be the classical
Picard number of the Fermat surface (Aoki (0.2)); values remembered by the referee, not by the paper:
  m=4: 20, m=6: 86, m=8: 176. (m = 10, 12 printed for the record.)
Cost prediction: (2,35): C(39,6) = 3,262,623 multisets in chunks of 100k, 24 units: ~12 s;
(2,25): C(29,6) = 475,020: ~2 s; k=1 ordered: (m-1)^2 grid per a0, trivial. Total < 30 s, < 100 MB.
"""
import sys, time, itertools
from math import comb, factorial, gcd
from fractions import Fraction
import numpy as np

T0 = time.time()

def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]

def Q_formula(k, m):
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

def pair_flags(A, m):
    """rows of A: tuples of nonzero residues mod m (m odd). True iff multiset splits into {a, m-a}."""
    rows, N = A.shape
    h = (m - 1) // 2
    cls = np.minimum(A, m - A) - 1
    sgn = np.where(A < m / 2.0, 1, -1).astype(np.int64)
    flat = (np.arange(rows)[:, None] * h + cls).ravel()
    D = np.bincount(flat, weights=sgn.ravel(), minlength=rows * h).reshape(rows, h)
    return np.all(D == 0, axis=1)

def count_multiset(k, m, chunk=100000):
    N = 2 * k + 2
    U = units(m)
    target = m * (k + 1)
    Nfact = factorial(N)
    totA = totB = totD = 0
    pnh = 0
    it = itertools.combinations_with_replacement(range(1, m), N)
    while True:
        block = list(itertools.islice(it, chunk))
        if not block:
            break
        A = np.array(block, dtype=np.int32)
        del block
        rows = A.shape[0]
        runidx = np.ones((rows, N), dtype=np.int64)
        for j in range(1, N):
            runidx[:, j] = np.where(A[:, j] == A[:, j - 1], runidx[:, j - 1] + 1, 1)
        w = Nfact // np.prod(runidx, axis=1)
        inA = (A.sum(axis=1) % m) == 0
        hodge = np.ones(rows, dtype=bool)
        for t in U:
            hodge &= (((t * A) % m).sum(axis=1) == target)
        pair = pair_flags(A, m) if m % 2 == 1 else np.zeros(rows, dtype=bool)
        totA += int(w[inA].sum()); totB += int(w[hodge].sum()); totD += int(w[pair].sum())
        pnh += int(np.sum(pair & ~hodge))
    return totA, totB, totD, pnh

def count_ordered_k1(m):
    """k = 1: enumerate all ordered (a0,a1,a2) in {1..m-1}^3, a3 := -(a0+a1+a2) mod m, keep a3 != 0."""
    U = units(m)
    target = 2 * m
    a1, a2 = np.meshgrid(np.arange(1, m), np.arange(1, m), indexing='ij')
    a1 = a1.ravel().astype(np.int64); a2 = a2.ravel().astype(np.int64)
    totA = totB = totD = 0
    pnh = 0
    for a0 in range(1, m):
        a3 = (-(a0 + a1 + a2)) % m
        keep = a3 != 0
        A = np.stack([np.full(keep.sum(), a0, dtype=np.int64), a1[keep], a2[keep], a3[keep]], axis=1)
        rows = A.shape[0]
        totA += rows
        hodge = np.ones(rows, dtype=bool)
        for t in U:
            hodge &= (((t * A) % m).sum(axis=1) == target)
        totB += int(hodge.sum())
        if m % 2 == 1:
            pair = pair_flags(A, m)
            totD += int(pair.sum())
            pnh += int(np.sum(pair & ~hodge))
    return totA, totB, totD, pnh

def show(k, m, res, expected_diff=None, note=""):
    N = 2 * k + 2
    A, B, D, pnh = res
    Af = ((m - 1) ** N + (-1) ** N * (m - 1)) // m
    Q = Q_formula(k, m) if m % 2 == 1 else None
    diff = B - Q if Q is not None else None
    flags = []
    if A != Af: flags.append("A-MISMATCH")
    if Q is not None and D != Q: flags.append("D!=Q")
    if pnh: flags.append("PAIR-NOT-HODGE")
    if expected_diff is not None:
        flags.append(f"paper says {expected_diff}: " + ("OK" if diff == expected_diff else "MISMATCH"))
    print(f"(k,m)=({k},{m}) N={N}: |A|={A} (formula {Af}) |B|={B} |D|={D} Q={Q} |B|-Q={diff} pair_not_hodge={pnh}",
          " ".join(flags), note, f"[{time.time()-T0:.1f}s]")
    sys.stdout.flush()

print("=== k = 1, ordered enumeration (independent of the multiset method) ===")
for m, exp in [(9, 48), (15, 288), (27, 192), (45, 528), (25, 0), (35, 0), (49, 0), (55, 0), (77, 0), (81, 624), (121, 0)]:
    show(1, m, count_ordered_k1(m), exp)

print("\n=== k = 2, multiset enumeration ===")
show(2, 25, count_multiset(2, 25), 2880)
show(2, 35, count_multiset(2, 35), 4320)

print("\n=== even m, k = 1: 1 + |B| vs classical Picard numbers (code sanity, not a claim of the paper) ===")
for m, rho in [(4, 20), (6, 86), (8, 176), (10, None), (12, None)]:
    A, B, D, pnh = count_ordered_k1(m)
    print(f"  m={m}: |A|={A}, |B|={B}, 1+|B|={1+B}", f"(remembered rho = {rho}: {'OK' if rho == 1+B else 'DIFFERENT'})" if rho else "")

print(f"\nTOTAL TIME {time.time()-T0:.1f}s")
