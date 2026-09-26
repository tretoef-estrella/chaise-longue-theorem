#!/usr/bin/env python3
"""
downset_bip_roots.py -- Theorem C at the roots: dim_F I^bal_a vs N_bal(a,q), dim_F I^ph_a vs N_ph(a,q),
from the definitions of Lemma 6.7(iii) and section 6.6 only.

usage:  downset_bip_roots.py (--bal A Q | --ph A Q) [--predict] [--single-bijection] [--char0] [--verbose]
  --single-bijection   negative control: use only sigma = identity instead of all of S_a
  --char0              also compute the rank over Q (exact, sympy DomainMatrix over QQ, degree by
                       degree) and mod the large prime 10007 as a proxy
"""
import argparse
import sys
import time

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from downset_bip_engine import *  # noqa
from downset_bip_engine import _mono_times  # noqa (not exported by import *)


def prime_of(q):
    p = min(f for f in range(2, q + 1) if q % f == 0)
    t = q
    while t > 1:
        assert t % p == 0
        t //= p
    return p


def char0_dims(ring, gens, log=None):
    """exact rank over Q of the ideal, degree by degree, with sympy (DomainMatrix over QQ)"""
    from sympy import QQ
    from sympy.polys.matrices import DomainMatrix
    total = 0
    dims = []
    for d in range(ring.maxdeg + 1):
        rows = []
        for g in gens:
            hom, e = ring.is_homogeneous(g)
            assert hom
            if e <= d:
                rows.append(_mono_times(ring, g, e, d))
        if not rows:
            dims.append(0)
            continue
        M = np.vstack(rows)
        M = M[np.any(M != 0, axis=1)]
        if M.shape[0] == 0:
            dims.append(0)
            continue
        dm = DomainMatrix([[QQ(int(x)) for x in row] for row in M.tolist()], M.shape, QQ)
        r = dm.rank()
        dims.append(r)
        total += r
        if log:
            log("    char 0, degree %2d: matrix %d x %d, rank %d" % (d, M.shape[0], M.shape[1], r))
    return total, dims


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bal", nargs=2, type=int)
    ap.add_argument("--ph", nargs=2, type=int)
    ap.add_argument("--predict", action="store_true")
    ap.add_argument("--single-bijection", action="store_true")
    ap.add_argument("--char0", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    T0 = time.time()
    if args.bal:
        a, q = args.bal
        alpha, beta = a, a
        name = "I^bal_%d" % a
    else:
        a, q = args.ph
        alpha, beta = a + 1, a
        name = "I^ph_%d" % a
    p = prime_of(q)
    print("%s at q = %d (p = %d), ring R_{[%d],[%d]} of dimension %d, date %s" % (
        name, q, p, alpha, beta, q ** (alpha + beta), now()))
    ring = BoxRing(alpha, beta, q)
    print("degrees 0..%d, n_d = %s" % (ring.maxdeg, ring.n_by_deg))

    # the counts, by their definitions (direct enumeration of Omega^alpha x Omega^beta)
    t0 = time.time()
    if args.bal:
        N = N_bal_direct(a, q)
        print("N_bal(%d,%d) by direct enumeration of %d points = %d   [%.1fs]; paper's closed form "
              "sum (a!/prod c_i!)^2 = %d (claim)" % (a, q, q ** (2 * a), N, time.time() - t0, N_bal_formula(a, q)))
    else:
        N = N_ph_direct(a, q)
        print("N_ph(%d,%d) by direct enumeration of %d points = %d   [%.1fs]; N_bal(%d,%d) direct = %d" % (
            a, q, q ** (2 * a + 1), N, time.time() - t0, a + 1, q, N_bal_direct(a + 1, q)))

    if args.predict:
        ng = math.factorial(a) if args.bal else (a + 1) * math.factorial(a)
        if args.single_bijection:
            ng = 1
        e = (q - 1) * a
        mm, el = cost_model(ring, {e: ng})
        nmax = max(ring.n_by_deg)
        print("PREDICTION: dim_F %s = %d (Thm C says >= %d; Cor 7.8 says =)%s" % (
            name, N, N, " -- negative control: expected < N" if args.single_bijection else ""))
        # memory: per degree d the direct method holds a row block (ng * n_{d-e}) x n_d (int32),
        # a basis of at most min(rows, n_d) x n_d (float32) and small batches; plus the ring tables
        # and ng dense generators; plus ~60 MB baseline
        peak = 0
        for d in range(e, ring.maxdeg + 1):
            rows = ng * ring.n_by_deg[d - e]
            peak = max(peak, rows * ring.n_by_deg[d] * 4 + min(rows, ring.n_by_deg[d]) * ring.n_by_deg[d] * 4)
        print("ESTIMATE: %d generators of degree %d; matmul %.2e flops + elimination %.2e ops -> raw model ~%.0f s, "
              "calibrated ~%.0f s (x%.2f) (+ enumeration of %d points, + char-0 sympy ranks if --char0); "
              "memory ~%.0f MB (per-degree peak of row block + basis) + %.0f MB tables/generators + 60 MB baseline" % (
                  ng, e, mm, el, estimate_seconds(mm, el), estimate_seconds(mm, el) * EMPIRICAL_FACTOR, EMPIRICAL_FACTOR,
                  ring.N, peak / 1e6, ring.N * (ring.nv * 8 * 3 + 8 * ng) / 1e6))
        return

    t0 = time.time()
    gens = gens_I_bal(ring, a) if args.bal else gens_I_ph(ring, a)
    if args.single_bijection:
        gens = gens[:1]
        print("NEGATIVE CONTROL: only the first generator (sigma = identity) is used")
    print("%d generators, built in %.1fs; degrees %s" % (
        len(gens), time.time() - t0, sorted(set(ring.is_homogeneous(g)[1] for g in gens))))
    t0 = time.time()
    dim, dims, _ = ideal_dims_graded(ring, gens, p, log=(print if args.verbose else None))
    print("dim_{F_%d} %s = %d   (per degree: %s)   [%.1fs]" % (p, name, dim, dims, time.time() - t0))
    if dim < N:
        verdict = "*** dim < N: CONTRADICTS THEOREM C ***"
    elif dim == N:
        verdict = "dim = N (Theorem C holds with equality here, as Cor. 7.8 claims)"
    else:
        verdict = "dim > N (Theorem C holds; contradicts the equality of Cor. 7.8)"
    print("RESULT %s q=%d: dim = %d, N = %d -> %s" % (name, q, dim, N, verdict))

    if args.char0:
        t0 = time.time()
        d0, dims0 = char0_dims(ring, gens, log=(print if args.verbose else None))
        print("dim_Q %s (exact, sympy over QQ) = %d   (per degree: %s)   [%.1fs]" % (name, d0, dims0, time.time() - t0))
        t0 = time.time()
        dP, dimsP, _ = ideal_dims_graded(ring, gens, 10007)
        print("dim_{F_10007} %s (proxy for char 0) = %d   (per degree: %s)   [%.1fs]" % (name, dP, dimsP, time.time() - t0))
        print("CHAR0 %s q=%d: dim_Q = %d, dim_F10007 = %d, dim_F%d = %d, N = %d" % (name, q, d0, dP, p, dim, N))
    print("total %.1fs" % (time.time() - T0))


if __name__ == "__main__":
    main()
