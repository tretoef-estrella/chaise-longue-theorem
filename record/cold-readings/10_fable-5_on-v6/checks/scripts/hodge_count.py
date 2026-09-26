"""
hodge_count.py — referee's own count of Hodge characters (§10 of the paper; definitions taken from Aoki 1983 p. 23,
verified on the page image): for n = 2k, m,
   𝔄 = {α = (a_0..a_{n+1}) : 1 ≤ a_i ≤ m−1, Σ a_i ≡ 0 (mod m)},
   𝔅 = {α ∈ 𝔄 : Σ_i <t a_i mod m>/m = k+1 for every t ∈ (Z/m)^×},
   𝔇 = {α ∈ 𝔄 : the multiset {a_i} splits into pairs {a, m−a}}.
Counts ORDERED tuples, by enumerating multisets and multiplying by the number of distinct orderings.
Also Q_k(m) (paper's formula) and Lemma 10.4's C(2k+2,k+1)^3 at m = 9.
usage: python3 hodge_count.py k m [k m ...]
"""
import sys, itertools
from math import factorial, comb, gcd
from fractions import Fraction
from collections import Counter

def Qk(k, m):
    N = 2 * k + 2; h = (m - 1) // 2
    tot = Fraction(0)
    def rec(parts_left, remaining, acc):
        nonlocal tot
        if parts_left == 0:
            if remaining == 0: tot += acc
            return
        for b in range(remaining + 1):
            rec(parts_left - 1, remaining - b, acc / Fraction(factorial(b)) ** 2)
    rec(h, N // 2, Fraction(1))
    return int(tot * factorial(N))

def count(k, m):
    N = 2 * k + 2
    units = [t for t in range(1, m) if gcd(t, m) == 1]
    # only need t up to sign: <(-t)a> = m - <ta>, so the condition for t implies it for -t
    units_half = [t for t in units if t <= m // 2]
    nB = 0; nD = 0; nA = 0
    for ms in itertools.combinations_with_replacement(range(1, m), N):
        if sum(ms) % m:
            continue
        cnt = Counter(ms)
        orderings = factorial(N)
        for v in cnt.values():
            orderings //= factorial(v)
        nA += orderings
        ok = all(sum((t * a) % m for a in ms) == m * (k + 1) for t in units_half)
        if ok:
            nB += orderings
            # pair type?
            c = dict(cnt); pair = True
            for a in list(c):
                if c.get(a, 0) != c.get(m - a, 0):
                    pair = False; break
            if pair:
                nD += orderings
    return nA, nB, nD

if __name__ == '__main__':
    args = [int(x) for x in sys.argv[1:]]
    for k, m in zip(args[::2], args[1::2]):
        nA, nB, nD = count(k, m)
        Q = Qk(k, m)
        extra = ''
        if m == 9:
            extra = f"  Lemma 10.4 predicts |B| = C({2*k+2},{k+1})^3 = {comb(2*k+2,k+1)**3}"
        print(f"(k,m)=({k},{m}): |A|={nA} |B|={nB} |D|={nD} Q_k(m)={Q} |B|-Q={nB-Q}  [|D|==Q: {nD==Q}]{extra}", flush=True)
