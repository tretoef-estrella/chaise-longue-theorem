#!/usr/bin/env python3
"""
verifier-counterex_thm0b_algebraic_upper_bound.py

Concrete instance for the finding: "the upper bound  dim_F I <= |Gamma_J|  (Prop 2.1 / (6.1))
and hence Corollary 7.8 do not depend on topology: they use only Theorem 0(b) = [DS, Claim 4.3],
which is a point count (CRT) on mu_m^{n+1}".

Everything below is executed with NO topological input: only the definitions of psi_J
(paper §2 / DS line 326), Definition 1.3 (Gamma_K), the structure theorem for f.g. abelian
groups, and linear algebra over Q, F_3, F_81.

PREDICTIONS (written before running):
  A. |Gamma_J| = Q_k(m): (1,3)->6, (2,3)->20, (1,15)->546.
     common zeros of all psi_J on mu_m^{n+1} (= rank_Z A_J by Step 6(b)): 21, 223, 2829.
  B. rank over Q of the ideal (psi_J) in Q[G]: (1,3)->6, (2,3)->20  (= |Gamma|);
     rank over F_3 of the ideal: 6, 20  (<= the Q-rank; equality = Main Theorem there).
  C. Cor 7.8 at q=3: dim_{F_3} I^bal_1 = 3 (dim_Q 4); dim_{F_3} I^bal_2 = 15 (dim_Q 24);
     dim_{F_3} I^ph_1 = 15.
  D. (k,m)=(1,15), F = GF(81) (contains mu_5): sum over the 125 colourings c of dim pi_c(I) = 546;
     block at c=(zeta, zeta^-1, 1) has dim 6 = (q-1)*N_bal(1,3) = 2*3; every non-compatible
     colouring gives 0; block-by-block equality with N_1(c)*prod N_zeta(c) (Lemma 6.8).
"""
import itertools, sys, time
import numpy as np
import sympy as sp
from fractions import Fraction
from math import comb, factorial

t_start = time.time()

# ---------------------------------------------------------------- matchings
def matchings(N):
    """perfect matchings of {0..N-1} as lists of (j,k) with j<k, first pair contains 0."""
    def rec(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for b in rest[1:]:
            r2 = [x for x in rest if x not in (a, b)]
            for m in rec(r2):
                yield [(a, b)] + m
    return list(rec(list(range(N))))

def Q_k(k, q):
    """Q_k(q) = N! [x^N] I_0(2x)^h, N=2k+2, h=(q-1)/2, exact."""
    N = 2 * k + 2; h = (q - 1) // 2
    # I_0(2x) = sum_b x^{2b}/(b!)^2 ; power h ; coefficient of x^N
    poly = {0: Fraction(1)}
    base = {2 * b: Fraction(1, factorial(b) ** 2) for b in range(0, N // 2 + 1)}
    for _ in range(h):
        new = {}
        for e1, c1 in poly.items():
            for e2, c2 in base.items():
                if e1 + e2 <= N:
                    new[e1 + e2] = new.get(e1 + e2, 0) + c1 * c2
        poly = new
    return int(poly.get(N, 0) * factorial(N))

# ------------------------------------------------- psi_J in the group ring Z[(Z/m)^{n+1}]
def psi_array(J, m, nv):
    """coefficient array of psi_J on (Z/m)^{nv}; variables t_1..t_nv are axes 0..nv-1 (index i -> axis i-1)."""
    shape = (m,) * nv
    f = np.zeros(shape, dtype=np.int64); f[(0,) * nv] = 1
    def mul_mono(g, exps):  # multiply by t^exps
        return np.roll(g, shift=exps, axis=tuple(range(nv)))
    for (j, kk) in J:
        # factor (t_k - 1)
        e = [0] * nv; e[kk - 1] = 1
        f = mul_mono(f, e) - f
        if j != 0:
            # factor phi(t_j t_k) = sum_{s} (t_j t_k)^s
            g = np.zeros_like(f)
            for s in range(m):
                e = [0] * nv; e[j - 1] = s; e[kk - 1] = s
                g += mul_mono(f, e)
            f = g
    return f

def gamma_K(K, m, nv):
    """Definition 1.3: exponent vectors a in (Z/m)^{nv} with a_i != 0 and some J in K with a_j + a_k = 0 (i>=1)."""
    G = set()
    for a in itertools.product(range(1, m), repeat=nv):
        for J in K:
            ok = True
            for (j, kk) in J:
                if j == 0: continue
                if (a[j - 1] + a[kk - 1]) % m != 0:
                    ok = False; break
            if ok:
                G.add(a); break
    return G

def rank_mod_p(M, p):
    """rank of integer matrix M over F_p (Gaussian elimination, numpy)."""
    A = np.array(M, dtype=np.int64) % p
    nrows, ncols = A.shape
    r = 0
    for c in range(ncols):
        if r >= nrows: break
        piv = np.nonzero(A[r:, c])[0]
        if piv.size == 0: continue
        pr = r + piv[0]
        if pr != r:
            A[[r, pr]] = A[[pr, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        others = np.nonzero(A[:, c])[0]
        others = others[others != r]
        if others.size:
            A[others] = (A[others] - np.outer(A[others, c], A[r])) % p
        r += 1
    return r

print("=" * 78)
print("PART A: Theorem 0(b) as a pure point count (Appendix B Step 6 / DS Claim 4.3)")
print("=" * 78)
resultsA = {}
for (k, m) in [(1, 3), (2, 3), (1, 15)]:
    n = 2 * k; nv = n + 1; N = n + 2
    JJ = matchings(N)
    G = gamma_K(JJ, m, nv)
    Qkm = Q_k(k, m)
    # numerical evaluation of psi_J at every point of mu_m^{nv} via the multidimensional DFT:
    # F[e] = sum_nu c_nu exp(-2 pi i nu.e/m) = psi_J(zeta^{-e}).
    nonzero = np.zeros((m,) * nv, dtype=bool)
    supp_sizes = []
    supp_crit = []
    for J in JJ:
        c = psi_array(J, m, nv)
        F = np.fft.fftn(c.astype(np.complex128))
        s = np.abs(F) > 1e-6 * max(1.0, np.abs(c).sum())
        supp_sizes.append(int(s.sum()))
        nonzero |= s
        # criterion of Step 6(b): psi_J(a) != 0 iff a_{k_i} != 1 for all i and a_{j_i} a_{k_i} = 1 (i>=1)
        cnt = 0
        for a in itertools.product(range(m), repeat=nv):
            ok = all(a[kk - 1] != 0 for (j, kk) in J) and all((a[j - 1] + a[kk - 1]) % m == 0 for (j, kk) in J if j != 0)
            cnt += ok
        supp_crit.append(cnt)
    common_zeros = int((~nonzero).sum())
    print(f"(k,m)=({k},{m}): #matchings={len(JJ)}, |Gamma_J| (Def 1.3, enumerated)={len(G)}, Q_k(m) formula={Qkm}")
    print(f"   support sizes of psi_J on mu_m^{nv} (DFT) = {supp_sizes}; by Step-6(b) criterion = {supp_crit}")
    print(f"   union of supports = {int(nonzero.sum())}  (should be |Gamma_J|={len(G)})")
    print(f"   common zeros = rank_Z A_J = dim_C(A_J (x) C) = {common_zeros}  (m^(n+1) - |Gamma| = {m**nv - len(G)})")
    assert len(G) == Qkm == int(nonzero.sum()) and common_zeros == m ** nv - len(G)
    resultsA[(k, m)] = (len(G), common_zeros)
print("  -> so dim_{F_p}(A_J (x) F_p) = rank + c_p >= m^(n+1) - |Gamma_J| for every p: this is the whole content")
print("     of the inequality of Prop 2.1, and dim_F I <= |Gamma_J| (6.1). No Pham cycle, no [DS, Thm 2.2].")

print()
print("=" * 78)
print("PART B: exact ranks of the ideal (psi_J) in Q[G] and F_3[G]")
print("=" * 78)
for (k, m) in [(1, 3), (2, 3)]:
    n = 2 * k; nv = n + 1; N = n + 2
    JJ = matchings(N)
    size = m ** nv
    rows = []
    for J in JJ:
        c = psi_array(J, m, nv)
        for e in itertools.product(range(m), repeat=nv):
            rows.append(np.roll(c, shift=e, axis=tuple(range(nv))).reshape(-1))
    M = np.array(rows, dtype=np.int64)
    r3 = rank_mod_p(M, 3)
    rbig = rank_mod_p(M, 10007)   # proxy for the Q-rank (rank_{F_l} <= rank_Q, equality for l not dividing torsion)
    if size <= 30:
        rQ = sp.Matrix(M.tolist()).rank()
    else:
        rQ = int(np.linalg.matrix_rank(M.astype(np.float64)))
    print(f"(k,m)=({k},{m}): ring dim {size}; rank_Q(psi_J) = {rQ} (exact sympy if dim<=30, else float SVD), rank_{{F_10007}} = {rbig}, rank_{{F_3}} = {r3}, |Gamma_J| = {resultsA[(k,m)][0]}")
    print(f"   dim_{{F_3}} A_J(x)F_3 = {size - r3} >= rank_Z A_J = {size - rQ}: inequality of Prop 2.1 (algebraic); equality here = no 3-torsion.")

print()
print("=" * 78)
print("PART C: Corollary 7.8 at q=3, direct linear algebra")
print("=" * 78)
def box_ideal_dims(gens_fn, nvars, q, p):
    """dims over F_p and Q of the ideal generated by polynomials (as dict monomial->coef) in F[x_1..x_nvars]/(x_i^q)."""
    monos = list(itertools.product(range(q), repeat=nvars))
    idx = {mo: i for i, mo in enumerate(monos)}
    rows = []
    for g in gens_fn():
        for mo in monos:
            v = [0] * len(monos)
            for e, cf in g.items():
                ee = tuple(a + b for a, b in zip(e, mo))
                if max(ee) < q:
                    v[idx[ee]] += cf
            rows.append(v)
    M = np.array(rows, dtype=np.int64)
    rp = rank_mod_p(M, p)
    rQ = sp.Matrix(M.tolist()).rank()
    return rp, rQ

def poly_pow_diff(i, j, nvars, e):
    """(x_i - x_j)^e as dict."""
    d = {}
    for s in range(e + 1):
        ex = [0] * nvars; ex[i] += s; ex[j] += e - s
        d[tuple(ex)] = d.get(tuple(ex), 0) + comb(e, s) * ((-1) ** (e - s))
    return d

def poly_mul(a, b):
    d = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            d[e] = d.get(e, 0) + c1 * c2
    return d

def N_bal(a, q):
    tot = 0
    for comp in itertools.product(range(a + 1), repeat=q):
        if sum(comp) == a:
            mult = factorial(a)
            for c in comp: mult //= factorial(c)
            tot += mult ** 2
    return tot

def N_ph(a, q):
    from collections import Counter
    cnt = 0
    for xi in itertools.product(range(q), repeat=a + 1):
        cx = Counter(xi)
        for eta in itertools.product(range(q), repeat=a):
            ce = Counter(eta)
            if all(cx[v] >= c for v, c in ce.items()):
                cnt += 1
    return cnt

q = 3
# I^bal_1: vars x1,z1  (indices 0,1)
def gens_bal1():
    yield poly_pow_diff(0, 1, 2, q - 1)
# I^bal_2: vars x1,x2,z1,z2 (0,1,2,3)
def gens_bal2():
    for sig in itertools.permutations(range(2)):
        g = {(0, 0, 0, 0): 1}
        for i in range(2):
            g = poly_mul(g, poly_pow_diff(i, 2 + sig[i], 4, q - 1))
        yield g
# I^ph_1: vars x1,x2,z1 (0,1,2): generators (x_i - z1)^{q-1}, i != i0
def gens_ph1():
    for i0 in range(2):
        i = 1 - i0
        yield poly_pow_diff(i, 2, 3, q - 1)
for name, fn, nvars, target in [("I^bal_1", gens_bal1, 2, N_bal(1, q)), ("I^bal_2", gens_bal2, 4, N_bal(2, q)), ("I^ph_1", gens_ph1, 3, N_ph(1, q))]:
    rp, rQ = box_ideal_dims(fn, nvars, q, 3)
    print(f"{name} at q=3: dim_{{F_3}} = {rp}, dim_Q = {rQ}, target N = {target}")

print()
print("=" * 78)
print("PART D: (k,m)=(1,15) over GF(81) ⊃ mu_5: the colour splitting, block by block")
print("=" * 78)
# ---- GF(81) = F_3[w]/(f), f irreducible quartic
w = sp.symbols('w')
fpoly = None
for coeffs in itertools.product(range(3), repeat=4):
    cand = sp.Poly([1] + list(coeffs), w, modulus=3)
    if cand.is_irreducible:
        fpoly = cand; break
fc = [int(x) % 3 for x in fpoly.all_coeffs()]  # leading first, degree 4
print("GF(81) = F_3[w]/(", fpoly.as_expr(), ")")
def to_digits(x):  # int 0..80 -> [c0,c1,c2,c3] coefficients of 1,w,w^2,w^3
    return [(x // 3 ** i) % 3 for i in range(4)]
def from_digits(d):
    return sum(int(d[i]) % 3 * 3 ** i for i in range(4))
def gf_mul_int(a, b):
    da, db = to_digits(a), to_digits(b)
    prod = [0] * 7
    for i in range(4):
        for j in range(4):
            prod[i + j] = (prod[i + j] + da[i] * db[j]) % 3
    # reduce modulo f (monic degree 4): w^4 = -(fc[1] w^3 + fc[2] w^2 + fc[3] w + fc[4])
    for dgr in range(6, 3, -1):
        c = prod[dgr]
        if c:
            prod[dgr] = 0
            for t in range(1, 5):
                prod[dgr - t] = (prod[dgr - t] - c * fc[t]) % 3
    return from_digits(prod[:4])
MUL = np.zeros((81, 81), dtype=np.int64)
ADD = np.zeros((81, 81), dtype=np.int64)
for a in range(81):
    for b in range(81):
        MUL[a, b] = gf_mul_int(a, b)
        ADD[a, b] = from_digits([(x + y) % 3 for x, y in zip(to_digits(a), to_digits(b))])
# sanity: field axioms spot check, find zeta of order 5
def gf_pow(a, e):
    r = 1
    for _ in range(e): r = int(MUL[r, a])
    return r
zeta = next(x for x in range(2, 81) if gf_pow(x, 5) == 1)
assert gf_pow(zeta, 5) == 1 and zeta != 1
mu5 = [gf_pow(zeta, e) for e in range(5)]
assert len(set(mu5)) == 5
print("zeta (primitive 5th root) =", zeta, "; mu_5 =", mu5)
DIG = np.array([to_digits(x) for x in range(81)], dtype=np.int64)  # 81 x 4

m, q, r = 15, 3, 5
k = 1; nv = 3; N = 4
JJ = matchings(N)
psis = [psi_array(J, m, nv) % 3 for J in JJ]   # entries 0,1,2 = elements of F_3 ⊂ GF(81)

def taylor_matrix(c):
    """T[j,i] = binom(i,j) mod 3 * c^{i-j} in GF(81): coefficient of u^j in t^i at t = c+u, u^3=0."""
    T = np.zeros((q, m), dtype=np.int64)
    for j in range(q):
        for i in range(m):
            if i >= j:
                T[j, i] = MUL[comb(i, j) % 3, gf_pow(c, i - j)]
    return T

def apply_axis(arr, T, axis):
    """GF(81)-linear map along one axis: out[j,...] = sum_i T[j,i] * arr[i,...]."""
    arr = np.moveaxis(arr, axis, 0)
    out = np.zeros((T.shape[0],) + arr.shape[1:], dtype=np.int64)
    for j in range(T.shape[0]):
        acc = np.zeros(arr.shape[1:], dtype=np.int64)
        for i in range(T.shape[1]):
            if T[j, i]:
                acc = ADD[acc, MUL[T[j, i], arr[i]]]
        out[j] = acc
    return np.moveaxis(out, 0, axis)

def block_dim(c):
    """dim_{GF(81)} of the ideal of R_c generated by the images of the psi_J (restriction of scalars to F_3)."""
    Ts = [taylor_matrix(ci) for ci in c]
    rows = []
    for ps in psis:
        g = ps.copy()
        for ax in range(nv):
            g = apply_axis(g, Ts[ax], ax)   # now shape (3,3,3) over GF(81)
        if not g.any():
            continue
        for alpha in itertools.product(range(q), repeat=nv):
            # multiply by u^alpha: shift with truncation
            h = np.zeros_like(g)
            sl_src = tuple(slice(0, q - a) for a in alpha)
            sl_dst = tuple(slice(a, q) for a in alpha)
            h[sl_dst] = g[sl_src]
            if not h.any():
                continue
            for e in range(4):        # scalars 1, w, w^2, w^3
                he = MUL[3 ** e, h]
                rows.append(DIG[he.reshape(-1)].reshape(-1))   # F_3-vector of length 27*4
    if not rows:
        return 0
    M = np.array(rows, dtype=np.int64)
    rk = rank_mod_p(M, 3)
    assert rk % 4 == 0
    return rk // 4

# ---- Lemma 6.8 side: block counts
def block_count(cexp):
    """cexp = (e1,e2,e3) exponents of colours c_i = zeta^{e_i}; returns (compatible, N_1, list of N_zeta, product)."""
    e0 = (-sum(cexp)) % r
    cols = [e0] + list(cexp)                    # colours of indices 0,1,2,3
    C = {z: [i for i in range(N) if cols[i] == z] for z in range(r)}
    compatible = (len(C[0]) % 2 == 0) and all(len(C[z]) == len(C[(-z) % r]) for z in range(1, r))
    if not compatible:
        return False, 0, [], 0
    # N_1(c)
    kk = len(C[0]) // 2
    if 0 in C[0]:
        N1 = Q_k(kk - 1, q) if kk >= 1 else 1
    else:
        N1 = comb(2 * kk, kk)        # 2k'-tuples in T (|T|=q-1=2) closed under the involution
    Ns = []
    for z in [1, 2]:                  # representatives of {1,4},{2,3}
        A, B = C[z], C[(-z) % r]
        alpha = len([i for i in A if i != 0]); beta = len([i for i in B if i != 0])
        if 0 not in A and 0 not in B:
            Ns.append(N_bal(alpha, q))
        else:
            Ns.append(N_ph(min(alpha, beta), q))
    prod = N1
    for x in Ns: prod *= x
    return True, N1, Ns, prod

total = 0; total_count = 0; mism = 0; ncomp = 0
special = None
for cexp in itertools.product(range(r), repeat=nv):
    c = [mu5[e] for e in cexp]
    d = block_dim(c)
    comp, N1, Ns, prod = block_count(cexp)
    total += d; total_count += prod
    ncomp += comp
    if d != prod:
        mism += 1
        print("   MISMATCH at colouring exps", cexp, ": dim", d, "count", prod)
    if cexp == (1, 4, 0):
        special = (d, N1, Ns, prod)
print(f"colourings: 125; compatible: {ncomp}; mismatches dim vs Lemma-6.8 count: {mism}")
print(f"sum_c dim pi_c(I) = dim_F I = {total};  Lemma 6.8 sum = {total_count};  |Gamma_J| = Q_1(15) = {Q_k(1, 15)}")
print(f"block of the Cor 7.8 colouring c=(zeta, zeta^-1, 1) [c_0=1]: dim = {special[0]}, N_1(c)={special[1]}, N_zeta={special[2]}, product={special[3]}")
print(f"   -> the pair block is I^bal_1 with dim {special[0] // special[1]} = N_bal(1,3) = {N_bal(1, 3)}: Corollary 7.8 at (a,q)=(1,3), obtained from (6.1) with zero topology.")
print(f"elapsed {time.time() - t_start:.1f} s")
