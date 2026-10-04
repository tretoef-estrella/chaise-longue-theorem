# f02_wing2.py — pilot. Leg F2: the tangent ideal inside the Theorem-B ideal of the odd number q + 1 (any characteristic).
#   box  B = F_p[s_1..s_n]/(s_i^q),  q = r + 1 even,  n = 2k+1
#   VV := ( Dt_J : J ),  Dt(a,b) = sum_{u=0}^{q-1} (-1)^u a^u b^(q-1-u)        (the D of Theorem B for the odd number q+1; dim = Q_k(q+1))
#   TT := Y * (D_{r,J}) C_r   (the tangent ideal; in characteristic 2 it is (L_J)B), dim = N_r(2k+2)
# Measured: dim VV, dim TT, TT inside VV, and dim (VV ∩ Y B) (the part of VV divisible by Y = s_1...s_n).
# Also the slices of TT against those of VV:  W_j(TT) = Y' * W_{j-1}(V)  and  W_j(VV).
# Usage: f02_wing2.py k q p
import sys, numpy as np
from eng import Box, Graded, ideal_from_generators, reorder, matchings, Dpoly, prod, N_odd, Q_free

def main(k, q, p):
    r = q - 1; n = 2 * k + 1
    box = Box([q] * n, p)
    Js = matchings(range(n + 1))
    gV, gT, free = [], [], []
    Y = box.poly([(1, {i: 1 for i in range(n)})])
    for J in Js:
        ks = [l - 1 for (j, l) in J]
        fV = prod(box, [Dpoly(box, j - 1, l - 1, q) for (j, l) in J if j != 0])
        fT = box.mul(Y, prod(box, [Dpoly(box, j - 1, l - 1, r) for (j, l) in J if j != 0]))
        gV.append(fV); gT.append(fT); free.append(ks)
    VV = ideal_from_generators(box, gV, free=free)
    TT = ideal_from_generators(box, gT, free=free)
    inside = VV.contains_space(TT)
    # VV ∩ Y B: monomials not divisible by Y first
    key = lambda E: (E.min(axis=1) >= 1).astype(np.int64)
    R = reorder(VV, key)
    inter = 0; hf_int = {}
    for d in R.rows:
        E, _, _ = R.columns(d)
        divis = (E.min(axis=1) >= 1)
        cnt = sum(1 for pos in R.pivots(d) if divis[pos])
        inter += cnt
        if cnt: hf_int[d] = cnt
    print(f"WING2 k={k} q={q} p={p}: dim VV={VV.dim()} (Q_k(q+1)={Q_free(q // 2, 2 * k + 2)})  dim TT={TT.dim()} (N_r={N_odd(r, 2 * k + 2)})  "
          f"TT inside VV: {inside}  dim(VV ∩ Y·B)={inter}  equal to TT: {inter == TT.dim()}", flush=True)
    print(f"      HF of TT: {TT.hf()}   HF of VV ∩ YB: {dict(sorted(hf_int.items()))}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
