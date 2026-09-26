# peelcore.py — functions of peelT.py (Fable, Mission 15), importable; set K, Q in sys.argv before import.
# peelT.py — Fable, Mission 15. Usage: python3 -u peelT.py K Q [show]
# Same KEY-lemma check as peel.py, but on multiset TYPES: the witness predicate is invariant under every bijection of
# F_q^x commuting with negation, so a multiset M is described by the multiset of unordered pairs (a >= b) =
# (multiplicities of u, -u) over the (q-1)/2 classes {u,-u} it meets.  Counts are weighted by the number of tuples.
import sys
from math import factorial
from functools import lru_cache
from collections import Counter
k, q = int(sys.argv[1]), int(sys.argv[2]); h = (q-1)//2
def feasible(m, t): return 2*t[0] + sum(t[1]) <= m
def canon(m, P): return frozenset(t for t in P if feasible(m, t))
def gr_ok(r, beta):
    for l in range(1, len(beta)+1):
        if sum(beta[:l]) > sum(min(x, l) for x in r): return False
    return True
@lru_cache(maxsize=None)
def witness(tau, s, beta):
    def rec(j, left, r):
        if left == 0: return gr_ok(r + [x for (a, b) in tau[j:] for x in (a, b)], beta)
        if j == len(tau): return False
        a, b = tau[j]
        for p in range(min(b, left), -1, -1):
            if rec(j+1, left-p, r + [a-p, b-p]): return True
        return False
    return rec(0, s, [])
@lru_cache(maxsize=None)
def inZ(tau, P): return any(witness(tau, s, beta) for (s, beta) in P)
def norm(pairs): return tuple(sorted((tuple(sorted(p, reverse=True)) for p in pairs if p != (0, 0)), reverse=True))
@lru_cache(maxsize=None)
def types(m):
    out = set()
    def rec(left, maxp, acc):
        if left == 0: out.add(norm(acc)); return
        if len(acc) == h: return
        for a in range(min(left, maxp[0]), 0, -1):
            for b in range(min(a, left-a), -1, -1):
                if (a, b) <= maxp: rec(left-a-b, (a, b), acc + [(a, b)])
    rec(m, (m, m), [])
    return sorted(out)
def count(tau):
    r = len(tau); c = Counter(tau)
    n = factorial(h) // factorial(h-r)
    for v in c.values(): n //= factorial(v)
    n *= 2**sum(1 for (a, b) in tau if a != b)
    m = sum(a+b for (a, b) in tau); t = factorial(m)
    for (a, b) in tau: t //= factorial(a)*factorial(b)
    return n*t
def fibre(tau, P):
    f = 0; seen = set()
    for j, (a, b) in enumerate(tau):
        for side in (0, 1):
            nt = list(tau); nt[j] = (a+1, b) if side == 0 else (a, b+1)
            if inZ(norm(nt), P): f += 1
    if len(tau) < h and inZ(norm(list(tau) + [(1, 0)]), P): f += 2*(h-len(tau))
    return f
def children(m, P, i):
    out = set()
    for (s, beta) in P:
        out.add((s, beta))
        for j, b in enumerate(beta):
            if b-1 <= q-2-i:
                nb = list(beta[:j]) + list(beta[j+1:]) + ([b-1] if b-1 >= 2 else [])
                out.add((s, tuple(sorted(nb, reverse=True))))
        if s >= 1:
            nb = list(beta) + ([i+1] if i+1 >= 2 else [])
            out.add((s-1, tuple(sorted(nb, reverse=True))))
            for j, b in enumerate(beta):
                if b == i:
                    nb = list(beta[:j]) + list(beta[j+1:]) + [i+1]
                    out.add((s-1, tuple(sorted(nb, reverse=True))))
    return canon(m-1, out)
