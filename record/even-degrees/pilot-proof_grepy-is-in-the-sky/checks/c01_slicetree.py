# c01_slicetree.py — pilot. Leg C: the slice tree of the odd box, against the layers of the point set.
#   root: V = (D_{r,J} : J) in C_r = F_p[y_1..y_{2k+1}]/(y_i^r);  Lambda_root = {((1),0), ((),1)}  (one unpaired value, zero or not)
#   at each node (ideal V on the variables y_t..y_m, set Lambda of shapes): peel the first variable;
#   compare  dim W_{r-1-i}(V)  with  |Z_{Lambda_i}|,  Lambda_i = tails with more than i completions.
#   The same Lambda reached along different paths must give the same ideal (checked).
# For each node also: the degrees of its minimal generators.
# Usage: c01_slicetree.py k r p [maxnodes]
import sys, numpy as np
from eng import Box, Graded, ideal_from_generators, slices, N_odd
from a04_oddbox import gens_free
import shapes as sh

def mingens(S):
    """Number of minimal generators of the homogeneous ideal S in each degree."""
    box = S.box; out = {}
    for d in sorted(S.rows):
        if S.dim(d) == 0: continue
        prev = Graded(box)
        if d - 1 in S.rows:
            vecs = []
            for f in S.basis_polys(d - 1):
                for i in range(box.n):
                    beta = np.zeros(box.n, dtype=np.int64); beta[i] = 1
                    g = box.shift(f, beta)
                    if len(g[1]): vecs.append(prev.to_vec(d, g))
            if vecs: prev.add_vecs(d, vecs)
        new = S.dim(d) - prev.dim(d)
        if new: out[d] = new
    return out

def same(A, B):
    return A.dim() == B.dim() and A.contains_space(B)

def main(k, r, p, maxnodes=400):
    n = 2 * k + 1
    box = Box([r] * n, p)
    g, f = gens_free(box, k, r, True)
    V = ideal_from_generators(box, g, free=f)
    root = frozenset({((1,), 0), ((), 1)})
    seen = {}            # (m, Lambda) -> ideal
    todo = [(n, root, V)]
    nodes = 0; bad_dim = 0; bad_same = 0
    print(f"SLICE TREE k={k} r={r} p={p}: root dim={V.dim()} |Z|={sh.size(root, n, r)} N_r={N_odd(r, 2 * k + 2)}", flush=True)
    while todo:
        m, Lam, S = todo.pop()
        if (m, Lam) in seen: continue
        seen[(m, Lam)] = S
        nodes += 1
        zs = sh.size(Lam, m, r)
        mg = mingens(S) if nodes <= maxnodes else None
        ok = (S.dim() == zs)
        print(f"node m={m} Lambda={sh.show(Lam)}  |Z|={zs} dim={S.dim()} {'OK' if ok else 'MISMATCH'}  mingens(deg:number)={mg}", flush=True)
        if m == 0: continue
        Ls, F = sh.layers(Lam, m, r)
        box2, W = slices(S, 0)
        for i in range(r):
            Wi = W[r - 1 - i]; Li = Ls[i]
            zi = sh.size(Li, m - 1, r)
            if Wi.dim() != zi:
                bad_dim += 1
                print(f"   SLICE MISMATCH at m={m} i={i}: dim W_{r - 1 - i}={Wi.dim()}  |Z_Lambda_i|={zi}  Lambda_i={sh.show(Li)}", flush=True)
            key = (m - 1, Li)
            if key in seen:
                if not same(seen[key], Wi):
                    bad_same += 1
                    print(f"   NOT THE SAME IDEAL for the same Lambda at m={m - 1}: {sh.show(Li)}", flush=True)
            elif Wi.dim() or zi:
                if not any(t[0] == key[0] and t[1] == key[1] for t in todo):
                    todo.append((m - 1, Li, Wi))
                else:
                    other = next(t for t in todo if t[0] == key[0] and t[1] == key[1])
                    if not same(other[2], Wi):
                        bad_same += 1
                        print(f"   NOT THE SAME IDEAL for the same Lambda at m={m - 1}: {sh.show(Li)}", flush=True)
    print(f"SUMMARY k={k} r={r} p={p}: nodes={nodes}  slices whose dimension differs from the layer count: {bad_dim}  same-Lambda-different-ideal: {bad_same}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 400)
