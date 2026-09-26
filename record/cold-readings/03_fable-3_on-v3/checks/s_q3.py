"""(S) at q = 3: dim (D_J : J in JJ) C, C = F_3[y_1..y_n']/(y_i^2), n' = 2k+1, with lex leading monomials.
Compares graded ranks with ballot numbers and leading monomials with the set U (paths never below -1)."""
import sys, time, itertools, numpy as np
from math import comb
sys.path.insert(0, __file__.rsplit('/',1)[0])
from f3linalg import Echelon

def matchings(elems):
    if not elems: yield []; return
    a = elems[0]
    for i in range(1, len(elems)):
        b = elems[i]
        rest = elems[1:i] + elems[i+1:]
        for m in matchings(rest): yield [(a, b)] + m

def run(k):
    n = 2*k + 1
    t0 = time.time()
    # degree-u basis: u-subsets of range(n) sorted lex-descending as monomials (y_1 > y_2 > ...)
    # lex order on squarefree monomials: compare exponent vectors; y_U > y_V iff at first differing index i, i in U.
    def key(U):  # larger key = lex-larger monomial; exponent vector as tuple with 1 for present
        return tuple(1 if i in U else 0 for i in range(n))
    idx = {}
    bases = {}
    for u in range(n+1):
        subs = sorted(itertools.combinations(range(n), u), key=key, reverse=True)
        bases[u] = subs
        idx[u] = {U: j for j, U in enumerate(subs)}
    # generators D_J: pairs (a<b) of J not containing 0, over indices 1..n -> 0..n-1
    gens = []
    for J in matchings(list(range(n+1))):   # index set {0..n} = {0..2k+1}
        pairs = [(a-1, b-1) for (a, b) in J if a != 0]
        # expand prod (y_b - y_a)
        poly = {(): 1}
        for (a, b) in pairs:
            new = {}
            for mon, c in poly.items():
                new[tuple(sorted(mon + (b,)))] = (new.get(tuple(sorted(mon + (b,))), 0) + c) % 3
                new[tuple(sorted(mon + (a,)))] = (new.get(tuple(sorted(mon + (a,))), 0) - c) % 3
            poly = {m: c for m, c in new.items() if c}
        gens.append(poly)
    ncols = len(bases[k])
    E = Echelon(ncols)
    M = np.zeros((len(gens), ncols), dtype=np.int8)
    for r, poly in enumerate(gens):
        for mon, c in poly.items(): M[r, idx[k][mon]] = c
    for start in range(0, len(gens), 3000):
        E.add_many(M[start:start+3000])
    ranks = [E.rank()]
    lead = {k: sorted(E.pivots)}
    # propagate
    prev = E
    for u in range(k+1, n+1):
        ncols = len(bases[u]); E = Echelon(ncols)
        rows = []
        for r in prev.rows:
            nz = np.flatnonzero(r)
            for i in range(n):
                v = np.zeros(ncols, dtype=np.int8)
                for j in nz:
                    U = bases[u-1][j]
                    if i in U: continue
                    v[idx[u][tuple(sorted(U + (i,)))]] = r[j]
                if v.any(): rows.append(v)
        if rows:
            R = np.stack(rows)
            for start in range(0, len(R), 3000): E.add_many(R[start:start+3000])
        ranks.append(E.rank()); lead[u] = sorted(E.pivots); prev = E
    total = sum(ranks)
    ballot = [comb(n, u) - comb(n, u+2) for u in range(k, n+1)]
    # U-set check
    def in_U(U):
        h = 0
        for i in range(n):
            h += 1 if i in U else -1
            if h < -1: return False
        return True
    ok = True
    for u in range(k, n+1):
        LM = set(bases[u][p] for p in lead[u])
        UU = set(U for U in bases[u] if in_U(U))
        if LM != UU: ok = False; print(f"  k={k} deg {u}: LM != U  (|LM|={len(LM)}, |U|={len(UU)}, LM-U={len(LM-UU)}, U-LM={len(UU-LM)})")
    print(f"k={k} n'={n}: total dim = {total} (Q_k(3)=C(2k+2,k+1)={comb(2*k+2,k+1)}); graded = {ranks}; ballot = {ballot}; LM==U: {ok}; {time.time()-t0:.1f}s")
    return total, ranks, ok

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or [1,2,3,4,5,6]
    for k in ks: run(k)
