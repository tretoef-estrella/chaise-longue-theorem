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
def children(m, P, i, prov=None):
    out = set()
    for (s, beta) in P:
        out.add((s, beta))
        if prov is not None: prov.setdefault((s, beta), 'L1 from %s' % ((s, beta),))
        for j, b in enumerate(beta):
            if b-1 <= q-2-i:
                nb = list(beta[:j]) + list(beta[j+1:]) + ([b-1] if b-1 >= 2 else [])
                out.add((s, tuple(sorted(nb, reverse=True))))
                if prov is not None: prov.setdefault((s, tuple(sorted(nb, reverse=True))), 'L3 from %s (block %d, j>=%d)' % ((s, beta), b, b-1))
        if s >= 1:
            nb = list(beta) + ([i+1] if i+1 >= 2 else [])
            out.add((s-1, tuple(sorted(nb, reverse=True))))
            if prov is not None: prov.setdefault((s-1, tuple(sorted(nb, reverse=True))), 'L2 from %s (|S|=%d, i=%d)' % ((s, beta), i+1, i))
            for j, b in enumerate(beta):
                if b == i:
                    nb = list(beta[:j]) + list(beta[j+1:]) + [i+1]
                    out.add((s-1, tuple(sorted(nb, reverse=True))))
                    if prov is not None: prov.setdefault((s-1, tuple(sorted(nb, reverse=True))), "L2' from %s (block %d->%d)" % ((s, beta), i, i+1))
    return canon(m-1, out)
seen = {}; bad = []; strict = [0]
import os
CERT = open(os.environ['CERT'], 'w') if os.environ.get('CERT') else None
def check(m, P):
    if (m, P) in seen: return seen[(m, P)]
    if m == 0:
        seen[(m, P)] = 1 if (0, ()) in P else 0; return seen[(m, P)]
    Zs = sum(count(t) for t in types(m) if inZ(t, P))
    fib = {t: fibre(t, P) for t in types(m-1)}
    # breakpoints: A_i changes only when i crosses a fibre value; P_i only at i <= m or i >= q-1-m (rules)
    fvals = set(fib.values())
    brk = sorted(set(range(0, min(q-1, m+2))) | set(range(max(0, q-2-m-1), q-1)) | set(f for f in fvals if f < q-1) | set(f-1 for f in fvals if 0 < f <= q-1))
    brk = [i for i in brk if 0 <= i <= q-2]
    Pall = {}
    for i in range(q-2, -1, -1):
        if i > m+1 and i < q-2-m-1:
            Pall[i] = Pall[i+1]; continue
        Pall[i] = canon(m-1, set(children(m, P, i)) | (set(Pall[i+1]) if i+1 in Pall else set()))
    tot = sum(count(t)*fib[t] for t in fib)
    done = set()
    for i in brk + [i for i in range(q-1) if i not in set(brk) and False]:
        A = frozenset(t for t in fib if fib[t] > i); Pi = Pall[i]
        key = (A, Pi)
        if key in done: continue
        done.add(key)
        B = frozenset(t for t in fib if inZ(t, Pi))
        if CERT is not None:
            prov = {}
            for ii in range(i, q-1):
                if ii > m+1 and ii < q-2-m-1: continue
                children(m, P, ii, prov)
            CERT.write('NODE m=%d P=%s  i=%d  child P_i=%s\n' % (m, sorted(P), i, sorted(Pi)))
            for t in sorted(A):
                w = next((u for u in sorted(Pi) if witness(t, u[0], u[1])), None)
                CERT.write('   fibre(%s)=%d > %d  covered by %s  [%s]\n' % (t, fib[t], i, w, prov.get(w, '?')))
        if not A <= B: bad.append((m, sorted(P), i, sorted(Pi), sorted(A - B)[:3]))
        if A != B: strict[0] += 1
        if A: check(m-1, Pi)
    # every i in [0,q-2] is covered: between consecutive breakpoints neither A_i nor P_i changes
    assert tot == Zs, (m, P, tot, Zs)
    seen[(m, P)] = Zs; return Zs
from math import comb
from fractions import Fraction
def Q(k, q):
    n = 2*k+2; hh = (q-1)//2
    I = [Fraction(1, factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    p = [Fraction(1)] + [Fraction(0)]*n
    for _ in range(hh): p = [sum(p[j]*I[i-j] for j in range(i+1)) for i in range(n+1)]
    return int(p[n]*factorial(n))
z = check(2*k+1, canon(2*k+1, {(k, ())}))
if len(sys.argv) > 3:
    for (m, P) in sorted(seen, key=lambda x: -x[0]): print('  node m=%d |Z|=%d P=%s' % (m, seen[(m, P)], sorted(P)))
print('PEELT k=%d q=%d |Z_root|=%d Q=%d %s nodes=%d KEY-failures=%d strict=%d' % (k, q, z, Q(k, q), 'Z=Q' if z == Q(k, q) else 'Z!=Q', len(seen), len(bad), strict[0]), flush=True)
for b in bad[:10]: print('  FAIL m=%d P=%s i=%d P_i=%s missing=%s' % b)
