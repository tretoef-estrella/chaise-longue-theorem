# a04_oddbox.py — pilot. Leg A / R4: the odd box (O) with my own engine.
#   dim_{F_p} (D_{r,J} : J) C_r,  C_r = F_p[y_1..y_{2k+1}]/(y_i^r),  D_{r,J} = prod over the k pairs of J avoiding 0 of D_r(y_a, y_b)
# Usage: a04_oddbox.py k r p [nosign | drop]      (nosign: all coefficients +1;  drop: each matching removed in turn)
import sys
from eng import Box, matchings, Dpoly, prod, N_odd, ideal_from_generators

def gens_free(box, k, r, signed=True, Js=None):
    n = 2 * k + 1
    Js = matchings(range(n + 1)) if Js is None else Js
    gens, free = [], []
    for J in Js:
        fs, ks = [], []
        for (j, l) in J:
            ks.append(l - 1)                       # one variable per pair (the partner of 0 included)
            if j != 0:
                fs.append(Dpoly(box, j - 1, l - 1, r, signed))
        gens.append(prod(box, fs)); free.append(ks)
    return gens, free

def main(k, r, p, mode):
    n = 2 * k + 1
    box = Box([r] * n, p)
    target = N_odd(r, 2 * k + 2)
    if mode == "drop":
        Js = matchings(range(n + 1))
        dims = []
        for i in range(len(Js)):
            g, f = gens_free(box, k, r, True, Js[:i] + Js[i + 1:])
            dims.append(ideal_from_generators(box, g, free=f).dim())
        print(f"DROP k={k} r={r} p={p}: dimension with one matching removed, for each of the {len(Js)} matchings: {dims}   N_r={target}", flush=True)
        return
    g, f = gens_free(box, k, r, mode != "nosign")
    S = ideal_from_generators(box, g, free=f)
    d = S.dim()
    print(f"BOX k={k} r={r} p={p} mode={mode}: dim C={r ** n} dim ideal={d} N_r(2k+2)={target} equal={d == target}  HF={list(S.hf().values())} from degree {min(S.hf())}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else "signed")
