#!/usr/bin/env python3
"""
downset_bip_engine.py -- referee's engine for Theorem 7.6 / Theorem C of
"The Chaise Longue Theorem" (PAPER_OFICIAL_v6.md).

Written ONLY from the definitions of the paper:
  * S_t, weak dominance, Vandermonde Delta            (section 5.2)
  * rows r-bar / r-underbar, options mu - e_j, mu + e_j, mu |_| 1   (section 5.5)
  * I^bal_a, I^ph_a, N_bal, N_ph                      (sections 6.5, 6.6)
  * peeling W_j(V)                                    (section 7.1)
  * shape of a point, BPar_q(alpha,beta), Z_Lambda, tight patterns, V_Lambda  (section 7.2)
  * the q options of a tail and the layers Lambda_i   (section 7.3, lines 579-584)
Nothing is taken from the paper's claims, from its verification record (section 12) or from
any external repository.

Conventions.  Omega = {0..q-1}.  Variables: x_1..x_alpha are variables 0..alpha-1,
z_1..z_beta are variables alpha..alpha+beta-1.  A polynomial of the box ring
R = F[x,z]/(x_i^q, z_l^q) is a dense int64 vector of length q^(alpha+beta) indexed by
idx = sum_j e_j q^j (e_j = exponent of variable j, 0 <= e_j < q).  Integer coefficients are
kept (so the same generators serve for characteristic 0 and for F_p; reduction mod p is done
at the last moment).
"""
import itertools
import math
import sys
import time
from collections import Counter

import numpy as np


# ----------------------------------------------------------------------------------------
# partitions and weak dominance (section 5.2)
# ----------------------------------------------------------------------------------------
def partitions(n, max_part=None):
    """all partitions of n as non-increasing tuples (() for n = 0)"""
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for first in range(min(n, max_part), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def S_t(lam, t):
    """sum of the t largest parts, padded with zeros"""
    return sum(lam[:t])


def wdom_le(lam, mu):
    """lam <= mu in weak dominance: S_t(lam) <= S_t(mu) for all t >= 1.
    For t beyond both lengths S_t is constant, so t = 1..max(len) suffices."""
    T = max(len(lam), len(mu), 1)
    return all(S_t(lam, t) <= S_t(mu, t) for t in range(1, T + 1))


def conjugate(lam):
    """column lengths lam'_c, c = 1..lam_1"""
    if not lam:
        return ()
    return tuple(sum(1 for part in lam if part >= c) for c in range(1, lam[0] + 1))


def sort_part(parts):
    return tuple(sorted((x for x in parts if x > 0), reverse=True))


# ----------------------------------------------------------------------------------------
# BPar_q(alpha, beta) with the product order (section 7.2)
# ----------------------------------------------------------------------------------------
def bpar(alpha, beta, q):
    """pairs (lam_plus, lam_minus): |l+| - |l-| = alpha - beta, |l+| + |l-| <= alpha + beta,
    len(l+) + len(l-) <= q  (literal definition)"""
    out = []
    for sp in range(0, alpha + beta + 1):
        sm = sp - (alpha - beta)
        if sm < 0 or sp + sm > alpha + beta:
            continue
        for lp in partitions(sp):
            for lm in partitions(sm):
                if len(lp) + len(lm) <= q:
                    out.append((lp, lm))
    return out


def bpar_le(a, b):
    return wdom_le(a[0], b[0]) and wdom_le(a[1], b[1])


def all_downsets(elems, le=bpar_le):
    """all down-sets, as bitmasks over the list elems (brute force over subsets)"""
    N = len(elems)
    below = []
    for i in range(N):
        m = 0
        for j in range(N):
            if le(elems[j], elems[i]):
                m |= 1 << j
        below.append(m)
    res = []
    for mask in range(1 << N):
        ok = True
        m = mask
        while m:
            i = (m & -m).bit_length() - 1
            if below[i] & ~mask:
                ok = False
                break
            m &= m - 1
        if ok:
            res.append(mask)
    return res


def mask_to_set(mask, elems):
    return [elems[i] for i in range(len(elems)) if mask >> i & 1]


def fmt_pp(lam):
    """pretty print a pair of partitions"""
    def f(p):
        return "()" if not p else "(" + ",".join(map(str, p)) + ")"
    return f(lam[0]) + "|" + f(lam[1])


# ----------------------------------------------------------------------------------------
# shapes of points (section 7.2)
# ----------------------------------------------------------------------------------------
def shape(xi, eta):
    cx = Counter(xi)
    cy = Counter(eta)
    plus = []
    minus = []
    for u in set(cx) | set(cy):
        d = cx[u] - cy[u]
        if d > 0:
            plus.append(d)
        elif d < 0:
            minus.append(-d)
    return (sort_part(plus), sort_part(minus))


def shape_histogram(alpha, beta, q):
    """Counter: shape -> number of points (xi, eta) in Omega^alpha x Omega^beta with that shape"""
    hist = Counter()
    for pt in itertools.product(range(q), repeat=alpha + beta):
        hist[shape(pt[:alpha], pt[alpha:])] += 1
    return hist


def size_Z(mask, elems, hist):
    return sum(hist.get(elems[i], 0) for i in range(len(elems)) if mask >> i & 1)


# ----------------------------------------------------------------------------------------
# the q options of a tail and the layers (section 7.3, lines 579-584)
# ----------------------------------------------------------------------------------------
def options(mu, q):
    """the q shapes obtained by adding one value u at the peeled x-index to a tail of shape mu,
    listed with multiplicity (one per value u in Omega): for each residual value of R_- (row j
    of mu_-): (mu_+, mu_- - e_j); for each residual value of R_+ (row j of mu_+): (mu_+ + e_j, mu_-);
    for each of the q - l_+ - l_- other values: (mu_+ |_| 1, mu_-)."""
    mp, mm = mu
    out = []
    for j in range(len(mm)):
        new = list(mm)
        new[j] -= 1
        out.append((mp, sort_part(new)))
    for j in range(len(mp)):
        new = list(mp)
        new[j] += 1
        out.append((sort_part(new), mm))
    for _ in range(q - len(mp) - len(mm)):
        out.append((sort_part(list(mp) + [1]), mm))
    assert len(out) == q
    return out


def F_Lambda(mu, Lambda_set, q):
    return sum(1 for o in options(mu, q) if o in Lambda_set)


def layers(Lambda_set, alpha, beta, q):
    """Lambda_i = {mu in BPar_q(alpha-1, beta) : F_Lambda(mu) > i}, i = 0..q-1, as sets"""
    sub = bpar(alpha - 1, beta, q)
    F = {mu: F_Lambda(mu, Lambda_set, q) for mu in sub}
    return [frozenset(mu for mu in sub if F[mu] > i) for i in range(q)], F


# ----------------------------------------------------------------------------------------
# tight patterns (section 7.2) -- enumeration
# ----------------------------------------------------------------------------------------
def set_partitions_sizes(elems, sizes):
    """all set partitions of elems whose multiset of block sizes is `sizes` (each once)"""
    elems = sorted(elems)
    sizes = list(sizes)
    assert sum(sizes) == len(elems)

    def rec(rem, szs):
        if not rem:
            yield ()
            return
        first = rem[0]
        for s in sorted(set(szs)):
            others = list(szs)
            others.remove(s)
            for comb in itertools.combinations(rem[1:], s - 1):
                block = (first,) + comb
                rest = [e for e in rem if e not in block]
                for tail in rec(rest, others):
                    yield (block,) + tail

    yield from rec(elems, sizes)


def tight_patterns(lam, A, B):
    """yield (P, blocks_plus, blocks_minus): P = set of alpha-|l+| = beta-|l-| disjoint pairs (i,l),
    blocks_plus partition A \\ A(P) with sizes the column lengths of l+, blocks_minus likewise."""
    lp, lm = lam
    k = len(A) - sum(lp)
    assert k == len(B) - sum(lm) and k >= 0, (lam, A, B)
    for Asub in itertools.combinations(A, k):
        for Bperm in itertools.permutations(B, k):
            P = tuple(zip(Asub, Bperm))
            Arest = [i for i in A if i not in Asub]
            Brest = [l for l in B if l not in Bperm]
            for bp in set_partitions_sizes(Arest, conjugate(lp)):
                for bm in set_partitions_sizes(Brest, conjugate(lm)):
                    yield P, bp, bm


# ----------------------------------------------------------------------------------------
# the box ring and its polynomials
# ----------------------------------------------------------------------------------------
class BoxRing:
    def __init__(self, alpha, beta, q):
        self.alpha, self.beta, self.q = alpha, beta, q
        nv = alpha + beta
        self.nv = nv
        self.N = q ** nv
        idx = np.arange(self.N, dtype=np.int64)
        self.qpow = np.array([q ** j for j in range(nv)], dtype=np.int64)
        self.exps = np.stack([(idx // self.qpow[j]) % q for j in range(nv)], axis=1).astype(np.int64) \
            if nv > 0 else np.zeros((1, 0), dtype=np.int64)
        self.deg = self.exps.sum(axis=1)
        self.maxdeg = nv * (q - 1)
        self.by_deg = [np.flatnonzero(self.deg == d) for d in range(self.maxdeg + 1)]
        self.n_by_deg = [len(b) for b in self.by_deg]
        self.pos = np.empty(self.N, dtype=np.int64)
        for d in range(self.maxdeg + 1):
            self.pos[self.by_deg[d]] = np.arange(self.n_by_deg[d])
        self._shift_cache = {}

    def x(self, i):  # x_i, i = 1..alpha
        assert 1 <= i <= self.alpha
        return i - 1

    def z(self, l):  # z_l, l = 1..beta
        assert 1 <= l <= self.beta
        return self.alpha + l - 1

    def one(self):
        f = np.zeros(self.N, dtype=np.int64)
        f[0] = 1
        return f

    def mul_var(self, f, v):
        """f * (variable v) in the box ring"""
        out = np.zeros_like(f)
        mask = self.exps[:, v] < self.q - 1
        src = np.flatnonzero(mask)
        out[src + self.qpow[v]] = f[src]
        return out

    def mul_linear(self, f, a, u, b, v):
        """f * (a*var_u + b*var_v)"""
        return a * self.mul_var(f, u) + b * self.mul_var(f, v)

    def mul_poly(self, f, g):
        """f * g for dense polynomials (used for cross-checks only)"""
        out = np.zeros_like(f)
        for idx in np.flatnonzero(g):
            e = self.exps[idx]
            src = np.flatnonzero(np.all(self.exps + e < self.q, axis=1))
            out[src + int(e @ self.qpow)] += g[idx] * f[src]
        return out

    def is_homogeneous(self, f):
        s = np.flatnonzero(f)
        if len(s) == 0:
            return True, None
        ds = set(self.deg[s].tolist())
        return len(ds) == 1, ds.pop() if len(ds) == 1 else None

    def shift_map(self, d, v):
        """positions in degree d -> positions in degree d+1 after multiplying by var v (-1 if killed)"""
        key = (d, v)
        if key not in self._shift_cache:
            idxs = self.by_deg[d]
            e = self.exps[idxs, v]
            ok = e < self.q - 1
            tgt = -np.ones(len(idxs), dtype=np.int64)
            tgt[ok] = self.pos[idxs[ok] + self.qpow[v]]
            self._shift_cache[key] = tgt
        return self._shift_cache[key]

    def w_degree(self, v):
        """exponent of variable v of every monomial"""
        return self.exps[:, v]


def vandermonde_factor_pairs(block):
    """Delta(B) = prod_{c<c'} (y_{b_c'} - y_{b_c}) for B = {b_1 < ... < b_r}"""
    b = sorted(block)
    return [(b[c2], b[c1]) for c1 in range(len(b)) for c2 in range(c1 + 1, len(b))]


def pattern_product(ring, P, blocks_plus, blocks_minus):
    """prod_{(i,l) in P} (x_i - z_l)^{q-1} * prod_c Delta(x_{B+_c}) * prod_c Delta(z_{B-_c}),
    integer coefficients, in the box ring"""
    f = ring.one()
    for (i, l) in P:
        for _ in range(ring.q - 1):
            f = ring.mul_linear(f, 1, ring.x(i), -1, ring.z(l))
    for blk in blocks_plus:
        for (hi, lo) in vandermonde_factor_pairs(blk):
            f = ring.mul_linear(f, 1, ring.x(hi), -1, ring.x(lo))
    for blk in blocks_minus:
        for (hi, lo) in vandermonde_factor_pairs(blk):
            f = ring.mul_linear(f, 1, ring.z(hi), -1, ring.z(lo))
    return f


def generators_of_downset(ring, Lambda_list, dedupe=True, count_patterns=False, p=None):
    """the tight-pattern products of all lambda in Lambda on (A,B) = ([alpha],[beta]);
    returns list of integer dense polynomials (deduplicated up to sign if dedupe);
    with p given they are reduced mod p and stored as int16 (memory)"""
    A = list(range(1, ring.alpha + 1))
    B = list(range(1, ring.beta + 1))
    gens = []
    seen = set()
    npat = 0
    for lam in Lambda_list:
        for (P, bp, bm) in tight_patterns(lam, A, B):
            npat += 1
            f = pattern_product(ring, P, bp, bm)
            assert np.abs(f).max() < 2 ** 62
            nz = np.flatnonzero(f)
            assert len(nz) > 0, "zero pattern product?"
            if f[nz[0]] < 0:
                f = -f
            key = f.tobytes() if dedupe else npat
            if key in seen:
                continue
            seen.add(key)
            gens.append(np.mod(f, p).astype(np.int16) if p else f)
    if count_patterns:
        return gens, npat
    return gens


# ----------------------------------------------------------------------------------------
# root ideals (section 6.5) and counts (section 6.6), by their own definitions
# ----------------------------------------------------------------------------------------
def gens_I_bal(ring, a):
    """I^bal_a = (prod_i (x_i - z_{sigma(i)})^{q-1} : sigma in S_a) in R_{[a],[a]}"""
    assert ring.alpha == a and ring.beta == a
    gens = []
    for sigma in itertools.permutations(range(1, a + 1)):
        P = tuple((i, sigma[i - 1]) for i in range(1, a + 1))
        gens.append(pattern_product(ring, P, (), ()))
    return gens


def gens_I_ph(ring, a):
    """I^ph_a = (prod_{i != i0} (x_i - z_{sigma(i)})^{q-1} : i0 in [a+1], sigma: [a+1]\\{i0} -> [a] bij.)"""
    assert ring.alpha == a + 1 and ring.beta == a
    gens = []
    for i0 in range(1, a + 2):
        others = [i for i in range(1, a + 2) if i != i0]
        for sigma in itertools.permutations(range(1, a + 1)):
            P = tuple(zip(others, sigma))
            gens.append(pattern_product(ring, P, (), ()))
    return gens


def N_bal_direct(a, q):
    n = 0
    for pt in itertools.product(range(q), repeat=2 * a):
        if sorted(pt[:a]) == sorted(pt[a:]):
            n += 1
    return n


def N_ph_direct(a, q):
    n = 0
    for pt in itertools.product(range(q), repeat=2 * a + 1):
        X = Counter(pt[:a + 1])
        Y = Counter(pt[a + 1:])
        if all(Y[u] <= X[u] for u in Y):
            n += 1
    return n


def N_bal_formula(a, q):
    """the paper's closed form sum_{c_1+..+c_q = a} (a!/(c_1!...c_q!))^2 (a CLAIM, used only for
    comparison).  Computed as a!^2 [t^a] (sum_c t^c / c!^2)^q by a DP over the q slots (exact
    fractions); the brute-force enumeration of (a+1)^q compositions was too slow for q = 19."""
    from fractions import Fraction
    w = [Fraction(1, math.factorial(c) ** 2) for c in range(a + 1)]
    f = [Fraction(0)] * (a + 1)
    f[0] = Fraction(1)
    for _ in range(q):
        g = [Fraction(0)] * (a + 1)
        for s in range(a + 1):
            if f[s]:
                for c in range(a + 1 - s):
                    g[s + c] += f[s] * w[c]
        f = g
    val = f[a] * math.factorial(a) ** 2
    assert val.denominator == 1
    return int(val)


def N_bal_formula_bruteforce(a, q):
    tot = 0
    for comp in itertools.product(range(a + 1), repeat=q):
        if sum(comp) == a:
            m = math.factorial(a)
            for c in comp:
                m //= math.factorial(c)
            tot += m * m
    return tot


# ----------------------------------------------------------------------------------------
# exact linear algebra mod p: incremental reduced row echelon basis, BLAS-based
# ----------------------------------------------------------------------------------------
class Echelon:
    """Reduced row-echelon basis of a subspace of F_p^n, built incrementally.
    Entries are stored as exact small integers in float32 (or float64) so that the reduction
    of a batch against the basis is a BLAS matmul; all partial sums stay below 2^24 (2^53)."""

    def __init__(self, p, n, batch=128, ordered=False):
        """ordered=True: pivots are chosen as the first non-zero column of the remaining rows
        (so that, within ONE batch, every basis row's pivot is its leading entry -- needed by
        the slice computation of downset_bip_peel.py).  ordered=False (default): the pivot of a
        row is its own leading entry, cheaper; the basis is still reduced (pivot columns are
        unit vectors), which is all the rank computation needs."""
        self.p = int(p)
        self.n = int(n)
        self.batch = batch
        self.ordered = ordered
        self.dtype = np.float32 if self.n * (self.p - 1) ** 2 < 2 ** 24 else np.float64
        # the basis lives in a preallocated buffer that grows by doubling (appending with
        # np.vstack made the resident set grow without bound under macOS malloc)
        self._Bbuf = np.zeros((0, self.n), dtype=self.dtype)
        self._piv = np.zeros(self.n, dtype=np.int64)
        self.k = 0
        self.inv = np.array([0] + [pow(a, -1, self.p) for a in range(1, self.p)], dtype=np.int64)

    @property
    def rank(self):
        return self.k

    @property
    def B(self):
        return self._Bbuf[:self.k]

    @property
    def piv(self):
        return self._piv[:self.k]

    def _ensure(self, extra):
        need = self.k + extra
        if need > self._Bbuf.shape[0]:
            cap = max(need, min(self.n, 2 * self._Bbuf.shape[0]), min(self.n, 256))
            nb = np.zeros((cap, self.n), dtype=self.dtype)
            nb[:self.k] = self._Bbuf[:self.k]
            self._Bbuf = nb

    def add(self, N):
        p = self.p
        N = np.asarray(N)
        if N.ndim == 1:
            N = N[None, :]
        for s in range(0, N.shape[0], self.batch):
            if self.rank == self.n:
                return
            C = np.mod(N[s:s + self.batch], p).astype(self.dtype)
            if self.rank:
                C -= C[:, self.piv] @ self.B
                np.mod(C, p, out=C)
            C = C[np.any(C != 0, axis=1)]
            if C.shape[0] == 0:
                continue
            R, pcs = self._rref(C)
            if R.shape[0] == 0:
                continue
            if self.rank:
                # keep the old basis reduced w.r.t. the new pivots; fixed-size blocks so that
                # the temporaries are reused by the allocator
                Bv = self.B
                for a in range(0, self.k, 256):
                    blk = Bv[a:a + 256]
                    blk -= blk[:, pcs] @ R
                    np.mod(blk, p, out=blk)
            r = R.shape[0]
            self._ensure(r)
            self._Bbuf[self.k:self.k + r] = R
            self._piv[self.k:self.k + r] = pcs
            self.k += r

    def _rref(self, C):
        p = self.p
        m = C.shape[0]
        if not self.ordered:
            keep = []
            pcs = []
            for r in range(m):
                row = C[r]
                nz = np.flatnonzero(row)
                if nz.size == 0:
                    continue
                c = int(nz[0])
                if row[c] != 1:
                    row = np.mod(row * self.inv[int(row[c])], p)
                    C[r] = row
                col = C[:, c].copy()
                col[r] = 0
                nzr = np.flatnonzero(col)
                if nzr.size:
                    C[nzr] = np.mod(C[nzr] - np.outer(col[nzr], row), p)
                keep.append(r)
                pcs.append(c)
            return C[keep], np.array(pcs, dtype=np.int64)
        r = 0
        pcs = []
        while r < m:
            sub = C[r:]
            colnz = np.flatnonzero(np.any(sub != 0, axis=0))
            if colnz.size == 0:
                break
            c = int(colnz[0])
            i = r + int(np.flatnonzero(sub[:, c])[0])
            if i != r:
                C[[r, i]] = C[[i, r]]
            C[r] = np.mod(C[r] * self.inv[int(C[r, c])], p)
            col = C[:, c].copy()
            col[r] = 0
            nzr = np.flatnonzero(col)
            if nzr.size:
                C[nzr] = np.mod(C[nzr] - np.outer(col[nzr], C[r]), p)
            pcs.append(c)
            r += 1
        return C[:r], np.array(pcs, dtype=np.int64)

    def basis_int(self):
        return np.rint(self.B).astype(np.int64)


def rank_mod_p_fast(M, p):
    E = Echelon(p, M.shape[1])
    E.add(M)
    return E.rank


# ----------------------------------------------------------------------------------------
# dimension of a homogeneous ideal, degree by degree
# ----------------------------------------------------------------------------------------
def _mono_times(ring, g_full, e, d, chunk=1_000_000):
    """rows m*g for all monomials m of degree d-e (g homogeneous of degree e), as an
    (n_{d-e} x n_d) integer matrix"""
    supp = np.flatnonzero(g_full)
    coef = g_full[supp]
    Eg = ring.exps[supp]                      # (s, nv)
    mons = ring.by_deg[d - e]
    Em = ring.exps[mons]                      # (m, nv)
    n_d = ring.n_by_deg[d]
    out = np.zeros((len(mons), n_d), dtype=np.int64 if coef.dtype == np.int64 else np.int32)
    s = len(supp)
    step = max(1, chunk // max(1, s * ring.nv))
    for a in range(0, len(mons), step):
        Emc = Em[a:a + step]
        sums = Emc[:, None, :] + Eg[None, :, :]          # (mc, s, nv)
        valid = np.all(sums < ring.q, axis=2)
        ri, ci = np.nonzero(valid)
        tgt = ring.pos[sums[ri, ci] @ ring.qpow]
        out[a + ri, tgt] = coef[ci]
    return out


def ideal_dims_graded(ring, gens, p, keep_bases=False, log=None, method="auto"):
    """dim_{F_p} of the ideal generated by the homogeneous polynomials gens (integer coeffs),
    computed degree by degree.  V_d = sum_v v*V_{d-1} + (generators of degree d)   [closure]
    or V_d = span{m*g : deg m = d - deg g}                                          [direct];
    both are spanning sets of V_d by the definition of the ideal generated by gens; the one
    with fewer rows is used.  Once V_{d-1} = R_{d-1}, V_d' = R_d' for all d' >= d because every
    box monomial of degree d' >= 1 is a variable times a box monomial of degree d'-1.
    Returns (total_dim, per-degree dims, per-degree bases if keep_bases)."""
    gens_by_deg = {}
    for g in gens:
        gm = np.mod(g, p)
        if not gm.any():
            continue
        hom, e = ring.is_homogeneous(gm)
        assert hom, "generator not homogeneous"
        gens_by_deg.setdefault(e, []).append(gm)
    dims = [0] * (ring.maxdeg + 1)
    bases = {}
    prev = None
    t0 = time.time()
    for d in range(ring.maxdeg + 1):
        n_d = ring.n_by_deg[d]
        prev_rank = prev.rank if prev is not None else 0
        if d >= 1 and prev_rank == ring.n_by_deg[d - 1]:
            for d2 in range(d, ring.maxdeg + 1):
                dims[d2] = ring.n_by_deg[d2]
                if keep_bases:
                    bases[d2] = np.eye(ring.n_by_deg[d2], dtype=np.int64)
            if log:
                log("    degree %d: V_{d-1} = R_{d-1}, so V_d' = R_d' for all d' >= %d" % (d, d))
            break
        have_gens = any(e <= d for e in gens_by_deg)
        if prev_rank == 0 and not have_gens:
            prev = Echelon(p, n_d)
            continue
        closure_rows = ring.nv * prev_rank + sum(len(v) for e, v in gens_by_deg.items() if e == d)
        direct_rows = sum(len(v) * ring.n_by_deg[d - e] for e, v in gens_by_deg.items() if e <= d)
        use_closure = (method == "closure") or (method == "auto" and closure_rows <= direct_rows)
        E = Echelon(p, n_d)
        if use_closure:
            if prev_rank:
                Bprev = prev.B
                rows = np.zeros((prev_rank, n_d), dtype=prev.dtype)
                for v in range(ring.nv):
                    sm = ring.shift_map(d - 1, v)
                    ok = sm >= 0
                    rows[:] = 0
                    rows[:, sm[ok]] = Bprev[:, ok]
                    E.add(rows)
                    if E.rank == n_d:
                        break
                del rows
            for g in gens_by_deg.get(d, []):
                E.add(g[ring.by_deg[d]])
        else:
            for e, v in sorted(gens_by_deg.items()):
                if e > d:
                    continue
                for g in v:
                    E.add(_mono_times(ring, g, e, d))
                    if E.rank == n_d:
                        break
                if E.rank == n_d:
                    break
        dims[d] = E.rank
        if keep_bases:
            bases[d] = E.basis_int()
        if log:
            log("    degree %2d: n_d = %5d, rows = %6d (%s), dim V_d = %5d   [%.1fs]" % (
                d, n_d, closure_rows if use_closure else direct_rows,
                "closure" if use_closure else "direct", E.rank, time.time() - t0))
        prev = E
    return sum(dims), dims, bases


def cost_model(ring, gens_degrees_counts, frac=0.5, batch=128):
    """rough cost of one ideal computation, used only for the time estimate in the log header:
    (matmul flops, elimination element-ops) = (sum_d rows_d * k_d * n_d, sum_d 3 * k_d * batch * n_d)
    with k_d ~ frac*n_d and rows_d = min(closure, direct) (closure with k_{d-1} ~ frac*n_{d-1})"""
    mm = 0.0
    el = 0.0
    for d in range(ring.maxdeg + 1):
        n_d = ring.n_by_deg[d]
        clo = ring.nv * frac * (ring.n_by_deg[d - 1] if d else 0)
        dire = sum(c * ring.n_by_deg[d - e] for e, c in gens_degrees_counts.items() if e <= d)
        if dire == 0:
            continue
        rows = min(clo, dire) if d else dire
        mm += rows * frac * n_d * n_d
        el += 3.0 * frac * n_d * min(batch, rows) * n_d
    return mm, el


# calibration constants (measured by downset_bip_calib.py on this machine; see its log)
RATE_MM = 5.0e9     # matmul model-flops per second (downset_bip_calib_2.log; model overestimates <= 2.5x)
RATE_EL = 2.0e8     # elimination element-ops per second (same log)


def estimate_seconds(mm, el):
    return mm / RATE_MM + el / RATE_EL


# observed on the audit cells (2,2,11) and (5,3,3): the model above (k_d ~ n_d/2 at every degree)
# overestimates the wall time 13-22x, because most degrees are empty or full; the drivers print
# both the raw model value and model/10 as the calibrated estimate
EMPIRICAL_FACTOR = 0.1


def now():
    return time.strftime("%Y-%m-%d %H:%M:%S")
