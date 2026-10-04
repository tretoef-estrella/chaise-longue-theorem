# c02_generators.py — pilot. Leg C: explicit generators of low degree of the nodes of the slice tree (run after c01).
# For each node it prints an echelon basis of the lowest degree of the ideal (these are minimal generators), as polynomials,
# with coefficients in the symmetric range. Variables are named by their original index (the tail of a node at level m is y_{n-m+1..n}).
# Usage: c02_generators.py k r p maxterms
import sys, numpy as np
from eng import Box, Graded, ideal_from_generators, slices
from a04_oddbox import gens_free
import shapes as sh

def polystr(f, names, p):
    E, c = f
    terms = []
    for e, co in zip(E, c):
        co = int(co)
        if p != 2 and co > p // 2: co -= p
        mon = "".join(f"{names[i]}^{a}" if a > 1 else names[i] for i, a in enumerate(e) if a)
        terms.append((("+" if co > 0 else "-") + (str(abs(co)) if abs(co) != 1 or not mon else "") + (mon or "")))
    return " ".join(terms) if terms else "0"

def main(k, r, p, maxterms):
    n = 2 * k + 1
    box = Box([r] * n, p)
    g, f = gens_free(box, k, r, True)
    V = ideal_from_generators(box, g, free=f)
    root = frozenset({((1,), 0), ((), 1)})
    seen = set(); todo = [(n, root, V)]
    while todo:
        m, Lam, S = todo.pop()
        if (m, Lam) in seen: continue
        seen.add((m, Lam))
        names = [f"y{i}" for i in range(n - m + 1, n + 1)]
        degs = sorted(d for d in S.rows if S.dim(d))
        if degs and 0 < m:
            d0 = degs[0]
            polys = S.basis_polys(d0)
            print(f"node m={m} Lambda={sh.show(Lam)}: lowest degree {d0}, {len(polys)} element(s)", flush=True)
            for q_ in polys[:8]:
                if len(q_[1]) <= maxterms:
                    print("     ", polystr(q_, names, p), flush=True)
                else:
                    print(f"      ({len(q_[1])} terms)", flush=True)
        if m == 0: continue
        Ls, F = sh.layers(Lam, m, r)
        box2, W = slices(S, 0)
        for i in range(r):
            if W[r - 1 - i].dim():
                todo.append((m - 1, Ls[i], W[r - 1 - i]))

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
