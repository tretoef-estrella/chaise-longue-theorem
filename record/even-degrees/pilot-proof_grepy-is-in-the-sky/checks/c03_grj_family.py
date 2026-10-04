# c03_grj_family.py — pilot. Leg C: is the peeling exact on a whole family of point sets, not only on the tree of the root?
# For EVERY pair (L0, L1) of down-sets (weak dominance) at level m:  V := gr J(Z_Lambda)  (grid T = {0} U mu_{r-1} in F_p),
#   test A:  W_{r-1-i}(V) = gr J(Z_{Lambda_i})  for every i (equality of ideals)
#   test B:  the layers of an interlaced pair are interlaced; and the options in Lambda form an initial segment of the chain
#            removals <= zero option <= middle <= additions
# The pairs are split into interlaced / not interlaced, and failures are reported for each kind.
# Also S6: the naive ideal (y_c^(r-1) D_r(y_a, y_b)) against gr J for the shape «one unpaired zero», m = 3.
# Usage: c03_grj_family.py r m p
import sys, numpy as np
from eng import Box, Graded, ideal_from_generators, slices, Dpoly
import shapes as sh
from grj import Grid, par, downsets, interlaced

def same(A, B):
    return A.dim() == B.dim() and A.contains_space(B)

def main(r, m, p):
    h = (r - 1) // 2
    G = Grid(r, m, p); G1 = Grid(r, m - 1, p)
    D0 = downsets(par(m, h)); D1 = downsets(par(m - 1, h))
    cache = {}
    def grj1(Lam):
        if Lam not in cache: cache[Lam] = G1.grJ(Lam)
        return cache[Lam]
    stats = {True: [0, 0, 0], False: [0, 0, 0]}        # [pairs, pairs with a failure of A, pairs whose layers are not interlaced]
    first_fail = {True: None, False: None}
    chain_fail = 0
    for L0 in D0:
        for L1 in D1:
            Lam = frozenset([(x, 0) for x in L0] + [(x, 1) for x in L1])
            if not Lam: continue
            il = interlaced(L0, L1)
            stats[il][0] += 1
            V = G.grJ(Lam)
            assert V.dim() == sh.size(Lam, m, r)
            Ls, F = sh.layers(Lam, m, r)
            box2, W = slices(V, 0)
            failA = False
            for i in range(r):
                if not same(W[r - 1 - i], grj1(Ls[i])):
                    failA = True
                    if first_fail[il] is None:
                        first_fail[il] = f"Lambda={sh.show(Lam)} i={i}: dim W_{r-1-i}={W[r-1-i].dim()} |Z_Lambda_i|={sh.size(Ls[i], m-1, r)} Lambda_i={sh.show(Ls[i])}"
                if il:
                    A0 = frozenset(x for (x, e) in Ls[i] if e == 0); A1 = frozenset(x for (x, e) in Ls[i] if e == 1)
                    if not interlaced(A0, A1): stats[il][2] += 1
            stats[il][1] += failA
            if il:      # chain test on every tail shape
                for (mu, eps) in sh.counts(m - 1, r):
                    l = len(mu)
                    rem = [(sh.norm(mu[:j] + (mu[j] - 1,) + mu[j + 1:]), eps) for j in range(l)]
                    add = [(sh.norm(mu[:j] + (mu[j] + 1,) + mu[j + 1:]), eps) for j in range(l - 1, -1, -1)]
                    mid = [(sh.norm(mu + (1,)), eps)] if h > l else []
                    chain = rem + [(mu, 1 - eps)] + mid + add
                    flags = [c in Lam for c in chain]
                    if any((not flags[t]) and flags[t + 1] for t in range(len(flags) - 1)): chain_fail += 1
    print(f"FAMILY r={r} m={m} p={p}: down-sets {len(D0)} x {len(D1)}", flush=True)
    for il in (True, False):
        print(f"   {'interlaced' if il else 'not interlaced'} pairs: {stats[il][0]};  pairs where some slice differs from gr J of the layer: {stats[il][1]}" +
              (f";  layers not interlaced: {stats[il][2]};  tails whose options in Lambda are not an initial segment: {chain_fail}" if il else ""), flush=True)
        if first_fail[il]: print("      first failure:", first_fail[il], flush=True)
    if m == 3:
        box = Box([r] * 3, p)
        naive = ideal_from_generators(box, [box.mul(box.var(c, r - 1), Dpoly(box, a, b, r)) for (c, a, b) in ((0, 1, 2), (1, 0, 2), (2, 0, 1))])
        tr = G.grJ(frozenset({((), 1)}))
        print(f"   S6: naive ideal (y_c^(r-1) D_r(y_a,y_b)) dim={naive.dim()}  gr J of «one unpaired zero» dim={tr.dim()}  points={sh.size(frozenset({((), 1)}), 3, r)}  naive inside: {tr.contains_space(naive)}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
