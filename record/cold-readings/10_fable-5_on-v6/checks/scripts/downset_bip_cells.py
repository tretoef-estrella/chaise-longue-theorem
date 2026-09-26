#!/usr/bin/env python3
"""
downset_bip_cells.py -- test Theorem 7.6 (dim_F V_Lambda >= |Z_Lambda|) for ALL down-sets
Lambda of BPar_q(alpha, beta) at one cell, from the definitions only (see downset_bip_engine.py).

usage:  downset_bip_cells.py --cell ALPHA BETA Q [--predict] [--crosscheck] [--verbose]
  --predict     no linear algebra: poset, down-sets, |Z_Lambda|, and time/memory estimate
  --crosscheck  (tiny cells) recompute every dim with gf_linalg.rank_mod_p on the full
                monomial-times-generator matrix (independent code path)
"""
import argparse
import sys
import time

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from downset_bip_engine import *  # noqa

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", nargs=3, type=int, required=True)
    ap.add_argument("--predict", action="store_true")
    ap.add_argument("--crosscheck", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--downsets", default=None,
                    help="only these down-set indices, e.g. 0-11 or 3,5,7 (the others are listed but not computed)")
    ap.add_argument("--time-cap", type=float, default=270.0,
                    help="stop computing further down-sets once this many seconds have elapsed (safety for the 5-minute cap)")
    args = ap.parse_args()
    selected = None
    if args.downsets:
        selected = set()
        for part in args.downsets.split(","):
            if "-" in part:
                lo, hi = part.split("-")
                selected.update(range(int(lo), int(hi) + 1))
            else:
                selected.add(int(part))
    alpha, beta, q = args.cell
    p = min(f for f in range(2, q + 1) if q % f == 0)
    v = 0
    t = q
    while t > 1:
        assert t % p == 0, "q must be a prime power"
        t //= p
        v += 1
    print("cell (alpha, beta, q) = (%d, %d, %d), p = %d, q = p^%d, F = F_%d, Omega = {0..%d}" % (
        alpha, beta, q, p, v, p, q - 1))
    print("date:", now())
    T0 = time.time()

    elems = bpar(alpha, beta, q)
    print("BPar_q(alpha,beta): %d elements:" % len(elems), " ".join(fmt_pp(e) for e in elems))
    nrel = sum(1 for a in elems for b in elems if a != b and bpar_le(a, b))
    print("strict order relations (product of weak dominance orders): %d" % nrel)
    dsets = all_downsets(elems)
    print("number of down-sets: %d" % len(dsets))

    hist = shape_histogram(alpha, beta, q)
    print("shape histogram over all %d points: %s" % (q ** (alpha + beta),
          " ".join("%s:%d" % (fmt_pp(k), c) for k, c in sorted(hist.items()))))
    print("set of shapes == BPar_q(alpha,beta)? %s" % (set(hist) == set(elems)))

    ring = BoxRing(alpha, beta, q)
    print("ring dimension q^(alpha+beta) = %d, degrees 0..%d, n_d = %s" % (
        ring.N, ring.maxdeg, ring.n_by_deg))

    # generator statistics per element (needed for both prediction and run)
    gen_info = {}
    for lam in elems:
        A = list(range(1, alpha + 1))
        B = list(range(1, beta + 1))
        pats = list(tight_patterns(lam, A, B))
        lp, lm = lam
        deg = (q - 1) * (alpha - sum(lp)) + sum(c * (c - 1) // 2 for c in conjugate(lp)) \
            + sum(c * (c - 1) // 2 for c in conjugate(lm))
        gen_info[lam] = (len(pats), deg)
    print("tight patterns per element (count, degree of product):",
          " ".join("%s:%d,%d" % (fmt_pp(l), *gen_info[l]) for l in elems))

    rows_summary = []
    print()
    print("down-sets (index: elements | |Z_Lambda| | dim V_Lambda):")
    est_mm = 0.0
    est_el = 0.0
    skipped = []
    for k, mask in enumerate(dsets):
        L = mask_to_set(mask, elems)
        Z = size_Z(mask, elems, hist)
        if not args.predict and ((selected is not None and k not in selected) or (time.time() - T0 > args.time_cap)):
            print("  #%2d: {%s} | |Z| = %d | NOT COMPUTED in this run (%s)" % (
                k, " ".join(fmt_pp(l) for l in L), Z,
                "not selected" if (selected is not None and k not in selected) else "time cap reached"))
            skipped.append(k)
            continue
        gdc = {}
        for lam in L:
            c, d = gen_info[lam]
            gdc[d] = gdc.get(d, 0) + c
        if args.predict:
            if L and not any(gen_info[lam][1] == 0 for lam in L):
                mm, el = cost_model(ring, gdc)
            else:
                mm, el = 0.0, 0.0
            est_mm += mm
            est_el += el
            print("  #%2d: {%s} | |Z| = %d | predicted dim = %d (equality measured by the paper; "
                  "Thm 7.6 says >=) | est %.1f s" % (k, " ".join(fmt_pp(l) for l in L), Z, Z, estimate_seconds(mm, el)))
            continue
        t0 = time.time()
        npat = 0
        if not L:
            dim, dims, ngens = 0, [0] * (ring.maxdeg + 1), 0
        elif any(gen_info[lam][1] == 0 for lam in L):
            # a tight pattern with no pairs and singleton blocks has product 1: V = R
            dim, dims, ngens = ring.N, list(ring.n_by_deg), None
        else:
            gens, npat = generators_of_downset(ring, L, count_patterns=True, p=p)
            ngens = len(gens)
            dim, dims, _ = ideal_dims_graded(ring, gens, p, log=(print if args.verbose else None))
        flag = "OK(=)" if dim == Z else ("dim>|Z|" if dim > Z else "*** dim<|Z| : CONTRADICTS THM 7.6 ***")
        extra = ""
        if args.crosscheck and L and ngens is not None:
            from gf_linalg import rank_mod_p
            rows = []
            for g in gens:
                for idx in range(ring.N):
                    mono = np.zeros(ring.N, dtype=np.int64)
                    mono[idx] = 1
                    rows.append(ring.mul_poly(g, mono))
            full = rank_mod_p(np.array(rows) % p, p)
            extra = " | crosscheck rank_mod_p(full matrix) = %d %s" % (full, "agree" if full == dim else "DISAGREE")
        print("  #%2d: {%s} | |Z| = %d | dim = %d | %s | gens %s | per-degree %s | %.1fs%s" % (
            k, " ".join(fmt_pp(l) for l in L), Z, dim, flag,
            ("%d (of %d patterns)" % (ngens, npat)) if ngens is not None else "(contains 1)",
            dims, time.time() - t0, extra))
        sys.stdout.flush()
        rows_summary.append((k, L, Z, dim))

    if args.predict:
        nmax = max(ring.n_by_deg)
        maxgens = max(sum(gen_info[l][0] for l in mask_to_set(m, elems)) for m in dsets)
        mem = 3 * nmax * nmax * 4 + ring.N * ring.nv * 8 * 3 + maxgens * ring.N * 2 * 2 + 60e6
        print()
        print("ESTIMATE: matmul %.2e flops + elimination %.2e ops -> raw model ~%.0f s (rates %.1e, %.1e per s), "
              "calibrated ~%.0f s (x%.2f, observed on (2,2,11),(5,3,3)); plus overhead ~%d down-sets x ~0.5 s; "
              "memory ~%.0f MB (3 float32 n_max^2 blocks, n_max = %d, ring tables, up to %d generators, baseline)" % (
                  est_mm, est_el, estimate_seconds(est_mm, est_el), RATE_MM, RATE_EL,
                  estimate_seconds(est_mm, est_el) * EMPIRICAL_FACTOR, EMPIRICAL_FACTOR, len(dsets),
                  mem / 1e6, nmax, maxgens))
        return

    lt = sum(1 for r in rows_summary if r[3] < r[2])
    gt = sum(1 for r in rows_summary if r[3] > r[2])
    eq = sum(1 for r in rows_summary if r[3] == r[2])
    print()
    print("SUMMARY cell=(%d,%d,%d) #down-sets=%d #computed=%d #dim<|Z|=%d #dim>|Z|=%d #equal=%d  total %.1fs%s" % (
        alpha, beta, q, len(dsets), len(rows_summary), lt, gt, eq, time.time() - T0,
        ("  NOT COMPUTED: %s" % skipped) if skipped else ""))
    # root cells, if present
    for k, L, Z, dim in rows_summary:
        if alpha == beta and L == [((), ())]:
            nb = N_bal_direct(alpha, q)
            print("ROOT I^bal_%d at q=%d: dim = %d, |Z_{(0,0)}| = %d, N_bal by direct count = %d, "
                  "paper's closed form = %d" % (alpha, q, dim, Z, nb, N_bal_formula(alpha, q)))
        if alpha == beta + 1 and L == [((1,), ())]:
            nph = N_ph_direct(beta, q)
            print("ROOT I^ph_%d at q=%d: dim = %d, |Z_{((1),0)}| = %d, N_ph by direct count = %d, "
                  "N_bal(%d,q) direct = %d" % (beta, q, dim, Z, nph, beta + 1, N_bal_direct(beta + 1, q)))


if __name__ == "__main__":
    main()
