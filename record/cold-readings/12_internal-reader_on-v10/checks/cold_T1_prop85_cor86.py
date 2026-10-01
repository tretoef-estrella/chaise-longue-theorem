# cold_T1: Proposition 8.5 (i)-(iii), Corollary 8.6 (i)-(ii), Remark 8.7(3) at small cells.
# Own engine (cold_lib).  Usage: python3 cold_T1_prop85_cor86.py
import sys, itertools, time
import numpy as np
from cold_lib import *

def rho_rank(box, Js, d, p):
    """rank of the stacked restriction maps C_d -> (+)_J F[x_b]/(x_b^r), x_a -> -x_b."""
    N, r = box.N, box.r
    src = box.mons.get(d, [])
    if not src:
        return 0
    rowidx = {}
    entries = []
    for jn, J in enumerate(Js):
        for ci, e in enumerate(src):
            sign = 1
            tgt = []
            ok = True
            for (a, b) in J:
                t = e[a] + e[b]
                if t >= r:
                    ok = False; break
                tgt.append(t)
                if e[a] % 2: sign = -sign
            if not ok: continue
            key = (jn, tuple(tgt))
            ri = rowidx.setdefault(key, len(rowidx))
            entries.append((ri, ci, sign))
    M = np.zeros((len(rowidx), len(src)), dtype=np.int64)
    for ri, ci, s in entries:
        M[ri, ci] += s
    return rank_mod(M, p)

def run_cell(r, N, primes, full_multipliers=True):
    box = Box(N, r)
    Js = list(matchings(range(N)))
    s = N // 2
    DJ = [D_J(N, r, J) for J in Js]
    # exact identities over Z (mod the box): (x_a+x_b) D_{r,J} = 0 and e_j D_{r,J} = 0 for odd j
    exact_ok = True
    for J, f in zip(Js, DJ):
        for (a, b) in J:
            if pmul(padd(var(N, a), var(N, b)), f, r):
                exact_ok = False
        for j in range(1, N + 1, 2):
            if pmul(elem_sym(N, j, r), f, r):
                exact_ok = False
    eodd = [elem_sym(N, j, r) for j in range(1, N + 1, 2)]
    if r % 2 == 0:
        walks = closed_walks(N, r // 2, False)
    else:
        walks = closed_walks(N, (r - 1) // 2, True)
    out = []
    for p in primes:
        t0 = time.time()
        # (i): for the first J (and all J if N<=4): dim D_J C_r = r^s ; dim I_J C_r = r^N - r^s
        chk_i = True
        Jtest = Js if N <= 4 else Js[:2]
        for J in Jtest:
            f = D_J(N, r, J)
            rkD = sum(span_rank_ideal(box, [f], p).values())
            lin = [padd(var(N, a), var(N, b)) for (a, b) in J]
            rkI = sum(span_rank_ideal(box, lin, p).values())
            if rkD != r ** s or rkI != r ** N - r ** s:
                chk_i = False
        # (ii): S = dim sum_J D_J C_r  ;  R = dim C_r / cap_J I_J C_r  via restriction maps
        if full_multipliers:
            Sd = span_rank_ideal(box, DJ, p)
        else:
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
        Rd = {d: rho_rank(box, Js, d, p) for d in range(box.top + 1)}
        R = sum(Rd.values())
        dual_ok = all(Sd[d] == Rd[box.top - d] for d in range(box.top + 1))
        # (iii) and quotient by (e_odd)
        Ed = span_rank_ideal(box, eodd, p)
        Q = box.total() - sum(Ed.values())
        # is  sum_J D_J C_r = ann(e_odd)?  (containment exact; equality iff S == Q)
        out.append((p, chk_i, S, R, dual_ok, Q, time.time() - t0))
    return exact_ok, walks, out

if __name__ == "__main__":
    cells = [(2, 2), (2, 4), (2, 6), (4, 2), (4, 4), (6, 4), (3, 2), (3, 4), (3, 6), (5, 2), (5, 4)]
    if len(sys.argv) > 1:
        cells = [tuple(int(t) for t in a.split(',')) for a in sys.argv[1:]]
    primes = [2, 3, 5, 1000003]
    for (r, N) in cells:
        exact_ok, walks, out = run_cell(r, N, primes)
        print(f"cell r={r} N={N}: exact identities over Z (x_a+x_b)D=0 and e_odd*D=0: {exact_ok}; walks={walks}", flush=True)
        for (p, chk_i, S, R, dual_ok, Q, dt) in out:
            print(f"   p={p}: (i) ann(D_J)=I_J [dims]: {chk_i} | (ii) dim Sum D_J C = {S}, dim C/cap(I_J) = {R}, equal: {S==R}, graded duality: {dual_ok} | "
                  f"(iii) dim C/(e_odd) = {Q}, S<=Q: {S<=Q} | S==walks: {S==walks} | ideals equal (S==Q): {S==Q}   [{dt:.1f}s]", flush=True)
    print("FIN-OK")
