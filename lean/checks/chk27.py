# Brute force for Lemma 6.8 (piece 27): |Gamma| = sum over compatible colourings of N_1(c) * prod_zeta N_zeta(c)
# mu_m modelled additively as Z/m; Z/m = Z/q x Z/r (CRT); colour = g mod r, w = g mod q.
import itertools, sys
from collections import Counter
from math import factorial

def closed(ms, mod):
    C = Counter(x % mod for x in ms)
    return all(C[x] == C[(-x) % mod] for x in C)

def gamma(m, n):
    cnt = 0
    for g in itertools.product(range(1, m), repeat=n+1):
        g0 = (-sum(g)) % m
        if g0 == 0: continue
        if closed((g0,)+g, m): cnt += 1
    return cnt

def Nbal(a, q):
    return sum(1 for x in itertools.product(range(q), repeat=a) for y in itertools.product(range(q), repeat=a) if Counter(x)==Counter(y))

def Nph(a, q):
    tot = 0
    for x in itertools.product(range(q), repeat=a+1):
        cx = Counter(x)
        for y in itertools.product(range(q), repeat=a):
            if not (Counter(y) - cx): tot += 1
    return tot

def N1(block, q):
    # block: indices in class of colour 0; w values in Z/q \ {0}; if 0 in block, w_0 = -(sum of other w in block)
    others = [i for i in block if i != 0]
    c = 0
    for w in itertools.product(range(1, q), repeat=len(others)):
        vals = list(w)
        if 0 in block:
            w0 = (-sum(w)) % q
            if w0 == 0: continue
            vals.append(w0)
        if closed(vals, q): c += 1
    return c

def formula(m, q, r, n, wrong=False):
    total = 0; ncol = 0
    for c in itertools.product(range(r), repeat=n+1):
        ext = ((-sum(c)) % r,) + c
        classes = {}
        for i, z in enumerate(ext): classes.setdefault(z, []).append(i)
        # compatible: class 0 even size, |C_z| = |C_-z|
        if len(classes.get(0, [])) % 2: continue
        if any(len(classes.get(z, [])) != len(classes.get((-z) % r, [])) for z in range(1, r)): continue
        ncol += 1
        prod = N1(classes.get(0, []), q)
        for z in range(1, r):
            if z > (-z) % r: continue  # representative
            A, B = classes.get(z, []), classes.get((-z) % r, [])
            al = len([i for i in A if i]); be = len([i for i in B if i])
            if 0 in A or 0 in B:
                prod *= (Nbal(min(al, be), q) if wrong else Nph(min(al, be), q))
            else:
                prod *= Nbal(al, q)
        total += prod
    return total, ncol

cells = [(15,2),(21,2),(45,2),(15,4)]
fails = 0; negfails = 0; checks = 0
for (m, n) in cells:
    G = gamma(m, n)
    for p in sorted({d for d in range(2, m+1) if m % d == 0 and all(d % e for e in range(2, d))}):
        q = 1
        while m % (q*p) == 0: q *= p
        r = m // q
        f, ncol = formula(m, q, r, n)
        fw, _ = formula(m, q, r, n, wrong=True)
        checks += 1
        ok = (f == G); fails += (not ok); negfails += (fw != G)
        print(f"m={m} n={n} p={p} q={q} r={r}: |Gamma|={G} sum={f} colourings={ncol} {'OK' if ok else 'FAIL'} | neg(ph->bal)={fw} {'fires' if fw!=G else 'SILENT'}", flush=True)
print(f"checks {checks}, failures {fails}, negative control fired {negfails}/{checks}")
