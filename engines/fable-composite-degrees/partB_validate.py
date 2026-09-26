"""Validate partB_engine on the paper's known cells: (D_J : J) C, C = F_p[y]/(y^{q-1})."""
import sys, time, itertools
from partB_engine import graded_dims, pmul
from math import comb

def D(a, b, nvars, q):
    out = {}
    for u in range(q - 1):
        e = [0] * nvars; e[a] = u; e[b] = q - 2 - u
        out[tuple(e)] = (-1) ** u
    return out

def matchings(items):
    if not items: yield []; return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]
        rest = items[1:i] + items[i+1:]
        for m in matchings(rest): yield [(a, b)] + m

def DJ_ideal_dims(k, q, p):
    nvars = 2 * k + 1
    gens = []
    for J in matchings(list(range(2 * k + 2))):
        g = {tuple([0] * nvars): 1}
        for (a, b) in J:
            if a == 0: continue
            g = pmul(g, D(a - 1, b - 1, nvars, q), box=q - 1)
        gens.append(g)
    return graded_dims(gens, nvars, q - 1, p)

for (k, q, p, expect) in [(1, 3, 3, 6), (2, 3, 3, 20), (3, 3, 3, 70), (1, 5, 5, 36), (1, 9, 3, 168), (2, 5, 5, 400), (1, 7, 7, 90)]:
    t0 = time.time()
    dims, tot = DJ_ideal_dims(k, q, p)
    print(f"(k,q)=({k},{q}) over F_{p}: dim = {tot} (expected Q_k(q) = {expect}) graded {list(dims.values())}  {time.time()-t0:.1f}s  {'OK' if tot == expect else 'FAIL'}")
