# patterns.py — pilot. Candidate generators («generalised tight patterns») for the odd box, defined over Z.
#   B(a,b)   := D_{r-1}(a,b) = sum_{u=0}^{r-2} (-1)^u a^u b^(r-2-u)       (antisymmetric, degree r-2)
#   D_r(a,b) := sum_{u=0}^{r-1} (-1)^u a^u b^(r-1-u)                      (symmetric, degree r-1)
#   Pf_E(M)  := Pfaffian of the antisymmetric matrix on M u E with entries B(y_i, y_j) (i, j in M), y_i^e (i in M, e in E), 0 (E x E)
# Pattern of an UNMARKED shape (lam, 0) on I: disjoint pairs P (factor D_r each) and column blocks B_c of lam (Vandermonde each).
# Pattern of a MARKED shape (lam, 1) on I:   pairs P (D_r each), column blocks B_c of lam for c >= 2 (Vandermonde each), and one
#   «marked block» M of size s + 2t, s = lam'_1 + 1, t >= 0, with the factor Pf_E(M): E = {r-1} if s = 1, E = {0, 1, .., s-3} if s >= 2.
import itertools, numpy as np
from eng import Box, Dpoly, prod

def Bpoly(box, a, b, r):
    return box.poly([((-1) ** u, {a: u, b: r - 2 - u}) for u in range(r - 1)])

def vandermonde(box, S):
    f = box.one()
    S = sorted(S)
    for i in range(len(S)):
        for j in range(i + 1, len(S)):
            f = box.mul(f, box.poly([(1, {S[j]: 1}), (-1, {S[i]: 1})]))
    return f

def pfaffian(box, idx, entry):
    """Pfaffian of the antisymmetric matrix entry(i, j), i < j in the list idx (expansion along the first index)."""
    if not idx: return box.one()
    if len(idx) % 2: return box.clean(np.zeros((0, box.n), dtype=np.int64), np.zeros(0, dtype=np.int64))
    a = idx[0]
    total = box.clean(np.zeros((0, box.n), dtype=np.int64), np.zeros(0, dtype=np.int64))
    for t in range(1, len(idx)):
        e = entry(a, idx[t])
        if e is None or len(e[1]) == 0: continue
        rest = idx[1:t] + idx[t + 1:]
        sub = pfaffian(box, rest, entry)
        if len(sub[1]) == 0: continue
        total = box.add(total, box.mul(e, sub), 1 if t % 2 == 1 else -1)
    return total

def pf_block(box, M, E, r):
    """Pf_E(M): M list of variables, E list of border exponents."""
    M = sorted(M)
    idx = [("v", i) for i in M] + [("e", e) for e in E]
    def entry(x, y):
        if x[0] == "v" and y[0] == "v": return Bpoly(box, x[1], y[1], r)
        if x[0] == "v" and y[0] == "e": return box.var(x[1], y[1]) if y[1] > 0 else box.one()
        return None
    return pfaffian(box, idx, entry)

def set_splits(I, sizes):
    """All ways to choose disjoint subsets of I with the given sizes (ordered list of sizes); yields (list of tuples, rest)."""
    if not sizes:
        yield [], tuple(I); return
    for S in itertools.combinations(I, sizes[0]):
        rest = [x for x in I if x not in S]
        for others, rr in set_splits(rest, sizes[1:]):
            yield [S] + others, rr

def matchings_of(I):
    I = list(I)
    if not I: yield []; return
    a = I[0]
    for t in range(1, len(I)):
        for Mx in matchings_of(I[1:t] + I[t + 1:]):
            yield [(a, I[t])] + Mx

def patterns(box, shape, r, absorb=True):
    """All pattern polynomials of the shape on the variables 0..n-1 of the box."""
    lam, eps = shape
    n = box.n
    cols = [sum(1 for x in lam if x >= c) for c in range(1, (lam[0] if lam else 0) + 1)]     # column lengths lam'_c
    out = []
    if eps == 0:
        if (n - sum(lam)) % 2 or n < sum(lam): return out
        for blocks, rest in set_splits(range(n), cols):
            V = prod(box, [vandermonde(box, S) for S in blocks])
            for P in matchings_of(rest):
                out.append(box.mul(V, prod(box, [Dpoly(box, a, b, r) for (a, b) in P])))
        return out
    s = (cols[0] if cols else 0) + 1
    other = cols[1:]
    free = n - sum(other) - s
    if free < 0 or free % 2: return out
    for t in range(0, free // 2 + 1 if absorb else 1):
        E = [r - 1] if s == 1 else list(range(0, s - 2))
        for blocks, rest in set_splits(range(n), other + [s + 2 * t]):
            Mb = blocks[-1]
            F = pf_block(box, list(Mb), E, r)
            if len(F[1]) == 0: continue
            V = box.mul(F, prod(box, [vandermonde(box, S) for S in blocks[:-1]]))
            for P in matchings_of(rest):
                out.append(box.mul(V, prod(box, [Dpoly(box, a, b, r) for (a, b) in P])))
    return out
