# c06_T3.py — pilot. Gate for Theorem T3 (the odd box r = 3 over every field).
# The family of ideals of C_m = F_p[y_1..y_m]/(y_i^3), with D(a,b) = y_a^2 - y_a y_b + y_b^2 and D_P = prod over the pairs of P:
#   J = m (mod 2):            I(m, J) = ( D_P : |P| = (m - J)/2 )
#   J != m (mod 2), J >= 1:   I(m, J) = ( (y_b - y_a) D_P : |P| = (m-1-J)/2 ;  D_P+ : |P+| = (m+1-J)/2 )
#   J = 0, m odd:             I(m, 0) = ( y_c^2 D_P : P perfect matching of the rest ;  Delta(a,b,c) D_P' : P' perfect matching of the rest )
# against  Z_J^(m) = { M in {-1,0,1}^m : |sum M| <= J }.
# Part 1: dim I(m, J) = |Z_J^(m)| for every 0 <= J <= m (the theorem gives >=; equality is measured).
# Part 2: the slice containments of the proof, as ideal memberships: W_2 >= I(m-1, J+1), W_1 >= I(m-1, J), W_0 >= I(m-1, J-1)
#         (for J = 0: W_2 >= I(m-1, 1)), and equality of the dimensions.
# Part 3: negative control: the same family with D(a,b) replaced by y_a^2 + y_a y_b + y_b^2 (wrong sign) in characteristic 3 and 101.
# Usage: c06_T3.py mmax p
import sys, itertools, numpy as np
from math import comb
from eng import Box, Graded, ideal_from_generators, slices, prod
from patterns import set_splits, matchings_of, vandermonde

def Dq(box, a, b, sign=-1):
    return box.poly([(1, {a: 2}), (sign, {a: 1, b: 1}), (1, {b: 2})])

def pair_sets(I, p):
    """All sets of p disjoint pairs inside the index list I; yields (list of pairs, rest)."""
    for S in itertools.combinations(I, 2 * p):
        rest = [x for x in I if x not in S]
        for P in matchings_of(S):
            yield P, rest

def gens(box, I, J, sign=-1):
    m = len(I); out = []
    if J >= m: return [box.one()]
    if J < 0: return []
    DP = lambda P: prod(box, [Dq(box, a, b, sign) for (a, b) in P])
    if (m - J) % 2 == 0:
        for P, rest in pair_sets(I, (m - J) // 2): out.append(DP(P))
    elif J >= 1:
        p = (m - 1 - J) // 2
        for P, rest in pair_sets(I, p):
            for a, b in itertools.combinations(rest, 2):
                out.append(box.mul(box.poly([(1, {b: 1}), (-1, {a: 1})]), DP(P)))
        for P, rest in pair_sets(I, p + 1): out.append(DP(P))
    else:
        for c in I:
            rest = [x for x in I if x != c]
            for P in matchings_of(rest): out.append(box.mul(box.var(c, 2), DP(P)))
        for T in itertools.combinations(I, 3):
            rest = [x for x in I if x not in T]
            for P in matchings_of(rest): out.append(box.mul(vandermonde(box, T), DP(P)))
    return out

def Zsize(m, J):
    if J < 0: return 0
    tot = 0
    for s in range(-min(J, m), min(J, m) + 1):
        # number of M in {-1,0,1}^m with sum s
        tot += sum(comb(m, a) * comb(m - a, a - s) for a in range(max(s, 0), m + 1) if 0 <= a - s <= m - a)   # a = number of +1, a - s = number of -1
    return tot

def ideal(box, I, J, sign=-1):
    g = [x for x in gens(box, I, J, sign) if len(x[1])]
    return ideal_from_generators(box, g) if g else Graded(box)

def main(mmax, p):
    bad = 0; badslice = 0; cells = 0
    for m in range(0, mmax + 1):
        box = Box([3] * m, p)
        for J in range(0, m + 1):
            V = ideal(box, list(range(m)), J)
            z = Zsize(m, J); cells += 1
            ok = V.dim() == z
            bad += (not ok)
            line = f"m={m} J={J}: dim I={V.dim()} |Z|={z} {'OK' if ok else 'MISMATCH'}"
            if m >= 1:
                box2, W = slices(V, 0)
                tail = list(range(m - 1))
                want = [(2, J + 1)] if J == 0 else [(2, J + 1), (1, J), (0, J - 1)]
                for (j, Jt) in want:
                    T = ideal(box2, tail, Jt)
                    inside = W[j].contains_space(T)
                    eq = inside and W[j].dim() == T.dim()
                    badslice += (not inside)
                    line += f"  W_{j}>=I(m-1,{Jt}): {inside}{'' if eq else ' (not equal!)'}"
            print(line, flush=True)
    print(f"T3 GATE p={p}: {cells} ideals; dimension != |Z| in {bad}; slice containments that fail: {badslice}", flush=True)
    if p != 2:
        # control: wrong sign
        diffs = []
        for m in range(1, min(mmax, 5) + 1):
            box = Box([3] * m, p)
            for J in range(0, m):
                V = ideal(box, list(range(m)), J, sign=+1)
                if V.dim() != Zsize(m, J): diffs.append((m, J, V.dim(), Zsize(m, J)))
        print(f"   CONTROL (y_a^2 + y_a y_b + y_b^2 instead of D), p={p}: cells (m, J, dim, |Z|) that differ: {diffs[:8]} ... {len(diffs)} in all", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
