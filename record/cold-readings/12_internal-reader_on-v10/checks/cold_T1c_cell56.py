# cold_T1c: the cell (r,N) = (5,6) (odd box, Remark 8.7(3)), reduced multipliers (one variable per pair), 4 characteristics.
# estimate: box 15625 monomials, largest graded piece 1751; largest matrix 5253 x 1751 int64 = 74 MB.
from cold_T1_prop85_cor86 import *
r, N = 5, 6
box = Box(N, r); Js = list(matchings(range(N))); s = 3
DJ = [D_J(N, r, J) for J in Js]
eodd = [elem_sym(N, j, r) for j in range(1, N + 1, 2)]
walks = closed_walks(N, 2, True)
for p in [2, 3, 5, 1000003]:
    Sd = {}
    for d in range(box.top + 1):
        rows = []
        for J, f in zip(Js, DJ):
            keep = set(b for (a, b) in J)
            for m in box.mons.get(d - s * (r - 1), []):
                if any(m[i] for i in range(N) if i not in keep): continue
                h = pmul(f, {m: 1}, r)
                if h: rows.append(vec(box, d, h, p))
        Sd[d] = rank_mod(np.array(rows), p) if rows else 0
    S = sum(Sd.values())
    R = sum(rho_rank(box, Js, d, p) for d in range(box.top + 1))
    Q = box.total() - sum(span_rank_ideal(box, eodd, p).values())
    print(f"r=5 N=6 p={p}: dim Sum D_J C = {S}  dim C/cap(I_J) = {R}  dim C/(e_odd) = {Q}  walks N_5(6) = {walks}  S==R: {S==R}  S==walks: {S==walks}  S==Q: {S==Q}", flush=True)
print("FIN-OK")
