# f01_homology.py — pilot. Leg F1: the homology of the «turn» on the tangent ideal, degree by degree, in characteristic 2.
# The tangent ideal of the even degree q is Y * V with V = (D_{r,J}) in C_r = F_2[y_1..y_n]/(y_i^r), r odd, n = 2k+1 (r = q - 1),
# and E = sum y_i^2 d/dy_i on Y*V corresponds on V to  E' = E + (y_1 + ... + y_n):   E'(y^alpha) = sum_{i : alpha_i even} y^(alpha + e_i).
# Output: dim V, rank of E', dimension of ker/im, and its distribution by degree (degrees of V; add n for the tangent ideal).
# Controls: E'^2 = 0 on V (checked on the basis); V is E'-stable (checked).
# Usage: f01_homology.py k r
import sys, numpy as np
from eng import Box, Graded, ideal_from_generators, N_odd
from a04_oddbox import gens_free

def Eprime(box, f):
    E, c = f
    out_E = []; 
    for i in range(box.n):
        sel = (E[:, i] % 2 == 0) & (E[:, i] + 1 < box.sizes[i])
        if sel.any():
            X = E[sel].copy(); X[:, i] += 1; out_E.append(X)
    if not out_E:
        return (np.zeros((0, box.n), dtype=np.int64), np.zeros(0, dtype=np.int64))
    X = np.concatenate(out_E)
    return box.clean(X, np.ones(len(X), dtype=np.int64))

def main(k, r):
    n = 2 * k + 1
    box = Box([r] * n, 2)
    g, f = gens_free(box, k, r, True)
    V = ideal_from_generators(box, g, free=f)
    degs = sorted(d for d in V.rows if V.dim(d))
    rank = {}; stable = True; sq = True
    for d in degs:
        img = Graded(box)
        vecs = []
        for b in V.basis_polys(d):
            eb = Eprime(box, b)
            if len(eb[1]):
                if not V.contains_vec(d + 1, V.to_vec(d + 1, eb)): stable = False
                if len(Eprime(box, eb)[1]): sq = False
                vecs.append(img.to_vec(d + 1, eb))
        if vecs: img.add_vecs(d + 1, vecs)
        rank[d] = img.dim(d + 1)
    hom = {d: V.dim(d) - rank.get(d, 0) - rank.get(d - 1, 0) for d in degs}
    tot = sum(hom.values()); R = sum(rank.values())
    print(f"TURN k={k} r={r} (q={r+1}): dim V={V.dim()} (N_r={N_odd(r, 2*k+2)})  E'-stable={stable}  E'^2=0: {sq}  rank E'={R}  homology={tot}  "
          f"by degree (from {degs[0]}): {[hom[d] for d in degs]}   HF: {[V.dim(d) for d in degs]}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
