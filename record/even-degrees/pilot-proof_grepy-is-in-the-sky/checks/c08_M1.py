# c08_M1.py — pilot. The one family of ideal memberships that the pencil constructions of Leg C do not cover:
#   (M1)(l, t):  Pf_{E_l}(M)  lies in the ideal  U_l(M) := ( Delta(S) * prod_{(a,b) in Q} D_r(y_a, y_b) :  S subset of M, |S| = l+1,
#                Q a perfect matching of M - S ),   |M| = l + 1 + 2t,   E_0 = {r-1},  E_l = {0, .., l-2} (l >= 1).
# Measured over F_p. Also reported: whether Pf vanishes identically, and whether it is a scalar multiple of the Vandermonde of M.
# Usage: c08_M1.py r l t p
import sys, itertools, numpy as np
from eng import Box, Graded, ideal_from_generators, Dpoly, prod
from patterns import pf_block, vandermonde, set_splits, matchings_of

def main(r, l, t, p):
    n = l + 1 + 2 * t
    box = Box([r] * n, p)
    E = [r - 1] if l == 0 else list(range(l - 1))
    P = pf_block(box, list(range(n)), E, r)
    gens = []
    for (S,), rest in set_splits(range(n), [l + 1]):
        for Q in matchings_of(rest):
            gens.append(box.mul(vandermonde(box, S), prod(box, [Dpoly(box, a, b, r) for (a, b) in Q])))
    if len(P[1]) == 0:
        print(f"M1 r={r} l={l} t={t} p={p}: the Pfaffian is identically zero (nothing to prove)", flush=True); return
    d = int(P[0][0].sum())
    U = Graded(box)
    # only the degree d of the ideal is needed
    for g in gens:
        d0 = int(g[0][0].sum())
        if d0 > d: continue
        from eng import monomials_of_degree
        vecs = []
        for mrow in monomials_of_degree(tuple([r] * n), d - d0):
            hpoly = box.shift(g, mrow)
            if len(hpoly[1]): vecs.append(U.to_vec(d, hpoly))
            if len(vecs) >= 400:
                U.add_vecs(d, vecs); vecs = []
        if vecs: U.add_vecs(d, vecs)
    inside = U.contains_vec(d, U.to_vec(d, P))
    V = vandermonde(box, list(range(n)))
    prop = len(V[1]) > 0 and int(V[0][0].sum()) == d
    print(f"M1 r={r} l={l} t={t} p={p}: {n} variables, deg Pf={d}, generators of U: {len(gens)} of degree {int(gens[0][0][0].sum())};  Pf in U: {inside}" +
          ("  (deg Pf = deg Vandermonde)" if prop else ""), flush=True)

if __name__ == "__main__":
    main(*[int(x) for x in sys.argv[1:5]])
