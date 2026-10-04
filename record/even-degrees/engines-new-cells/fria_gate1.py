# fria_gate1.py — cold audit, gate G1/G2: Theorem 6.1, Lemma 2.4 and Proposition 6.1 of PROOF_ODD_BOX.md, from the definitions (Grepy Chats, 2 Oct 2026).
# For every interlaced pair Lambda at the cell (r, m, p):
#   (a) dim V_Lambda >= |Z_Lambda| (and whether equal);  control: the same without absorbed pairs (t = 0 only);
#   (b) layers: the number of completions of a tail depends only on its shape and equals (2.1); every Lambda_i is interlaced; sum |Z_{Lambda_i}| = |Z_Lambda|;
#   (c) Proposition 6.1 as memberships: every pattern product of every shape of Lambda_i lies in the slice W_{r-1-i}(V_Lambda), the slices computed from the ideal.
import sys, itertools
from fria_engine import *
cells = [tuple(int(x) for x in a.split(',')) for a in sys.argv[1:]]
tot = dict(pairs=0, ge=0, eq=0, ctrl_fail=0, lay_bad=0, memb=0, memb_fail=0, slice_sum_bad=0)
for (r, m, p) in cells:
    h = (r - 1) // 2; R = Box(m, r, p); S = Sh(m, h)
    Vs = {s: R.ideal(pattern_products(R, s, list(range(m)))) for s in S}
    Vs0 = {s: R.ideal(pattern_products(R, s, list(range(m)), tmax=0)) for s in S}
    cnt = {}
    for M in itertools.product(range(-h, h + 1), repeat=m):
        sh = shape_of(M, h); cnt[sh] = cnt.get(sh, 0) + 1
    assert set(cnt) <= set(S), "a point has a shape outside Sh_m"
    IP = interlaced_pairs(m, h)
    if m >= 2:
        R1 = Box(m - 1, r, p); S1 = Sh(m - 1, h)
        prods1 = {s: pattern_products(R1, s, list(range(m - 1))) for s in S1}
    c = dict(pairs=0, ge=0, eq=0, ctrl_fail=0, lay_bad=0, memb=0, memb_fail=0, slice_sum_bad=0)
    for L in IP:
        V = R.add([Vs[s] for s in L]); dim = R.dim(V); z = sum(cnt.get(s, 0) for s in L)
        c['pairs'] += 1; c['ge'] += dim >= z; c['eq'] += dim == z
        V0 = R.add([Vs0[s] for s in L]); c['ctrl_fail'] += R.dim(V0) < z
        if dim < z: print(f"  !!! r={r} m={m} p={p} Lambda={sorted(L)}: dim {dim} < |Z| {z}", flush=True)
        if m >= 2:
            Li = layers_formula(L, m, h, r); by, sizes = layers_brute(L, m, h, r)
            ok = all(len(v) == 1 for v in by.values()) and all(next(iter(v)) == F_formula(L, s[0], s[1], h, r) for s, v in by.items())
            ok = ok and all((len(X) == 0 or is_interlaced(X, m - 1, h)) for X in Li) and sum(sizes) == z
            c['lay_bad'] += (not ok)
            S2, W = R.slices(V)
            if sum(R1.dim(w) for w in W) != dim: c['slice_sum_bad'] += 1
            for i in range(r):
                for s in Li[i]:
                    for G in prods1[s]:
                        c['memb'] += 1
                        if not R1.member(W[r - 1 - i], G): c['memb_fail'] += 1
    print(f"r={r} m={m} p={p}: interlaced pairs {c['pairs']}; dim>=|Z| {c['ge']}; equal {c['eq']}; control (no absorbed pairs) fails in {c['ctrl_fail']}; layer checks bad {c['lay_bad']}; slice-sum bad {c['slice_sum_bad']}; memberships {c['memb']}, failures {c['memb_fail']}", flush=True)
    for k in tot: tot[k] += c[k]
print("TOTAL", tot)
print("FIN-OK")
