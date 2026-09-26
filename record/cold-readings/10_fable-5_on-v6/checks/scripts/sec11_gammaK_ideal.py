#!/usr/bin/env python3
"""
Referee check for Section 11 (Corollary W(ii)) of PAPER_OFICIAL_v6.md.

Independent of the paper's code.  For small cells (m, d, s) we
  (A) enumerate Gamma_K for K = J(s,d) literally from [DS, Definition 1.3]
      and compare with the paper's count Q_s(m) (m-1)^{d-s};
  (B) compute dim_{F_p} of the ideal (psi_J : J in K) in the literal ring
      F_p[t_1..t_{2d+1}]/(t_i^m - 1) of [DS], with psi_J literally as in
      [DS, source line 326] (tau_J = prod (t_{k_i}-1), psi_J = tau_J prod_{i>=1} phi(t_{j_i} t_{k_i}))
      for every prime p | m, and compare with |Gamma_K| (equality <=> torsion free,
      by Proposition 2.1 of the paper / Theorem 1.1(a)+Claim 4.3 of [DS]).
  (C) check the pair-factor dimension: dim (t_b-1) phi(t_a t_b) in F_p[t_a,t_b]/(t^m-1) == m-1.
  (D) check the factorisation psi_J = psi_{J'} * prod g_i as polynomials (exact, over Z).
Predicted: < 60 s, < 100 MB.
"""
import sys, time, itertools
from fractions import Fraction
from math import factorial
import numpy as np

t_start = time.time()

# ---------- combinatorics ----------
def matchings(idx):
    """All perfect matchings of the sorted list idx, in DS form: list of [j,k] with j<k, sorted by j."""
    idx = list(idx)
    if not idx:
        return [[]]
    a = idx[0]
    out = []
    for b in idx[1:]:
        rest = [x for x in idx if x != a and x != b]
        for M in matchings(rest):
            out.append([[a, b]] + M)
    return out

def J_of(d):
    return matchings(range(0, 2 * d + 2))

def J_sd(s, d):
    """Matchings of {0..2d+1} containing the pairs {2i,2i+1} for s < i <= d."""
    tail = [[2 * i, 2 * i + 1] for i in range(s + 1, d + 1)]
    return [J for J in J_of(d) if all(p in J for p in tail)]

def Q(k, m):
    """Q_k(m) = (2k+2)! [x^{2k+2}] I_0(2x)^{(m-1)/2}."""
    h = (m - 1) // 2
    N = 2 * k + 2
    # series in x^2: I_0(2x) = sum_b x^{2b}/(b!)^2, truncate at b <= N//2
    B = N // 2
    base = [Fraction(1, factorial(b) ** 2) for b in range(B + 1)]
    poly = [Fraction(1)] + [Fraction(0)] * B
    for _ in range(h):
        new = [Fraction(0)] * (B + 1)
        for i, a in enumerate(poly):
            if a == 0:
                continue
            for j, b in enumerate(base):
                if i + j <= B:
                    new[i + j] += a * b
        poly = new
    return int(poly[B] * factorial(N))

def dfact(n):
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r

# ---------- (A) Gamma_K from Definition 1.3 ----------
def gamma_K_count(m, d, K):
    """a in mu_m^{2d+1} written as exponents e_i in Z/m; a_i != 1 <=> e_i != 0; a_j a_k = 1 <=> e_j+e_k = 0 mod m.
    Definition 1.3: a_i != 1 for all i=1..n+1, and exists J in K with a_{j_i} a_{k_i} = 1 for i = 1..d."""
    n1 = 2 * d + 1
    # enumerate exponent tuples with all e_i != 0
    count = 0
    pairs_list = [[(p[0], p[1]) for p in J[1:]] for J in K]  # pairs i >= 1 (the one containing 0 is J[0])
    for e in itertools.product(range(1, m), repeat=n1):
        ok = False
        for pl in pairs_list:
            good = True
            for (j, k) in pl:
                if (e[j - 1] + e[k - 1]) % m != 0:
                    good = False
                    break
            if good:
                ok = True
                break
        if ok:
            count += 1
    return count

# ---------- (B) literal ideal in F_p[G] ----------
def build_psi_vec(m, d, J):
    """psi_J as an integer vector on exponent tuples nu in (Z/m)^{2d+1} (index 1..2d+1 -> position 0..2d)."""
    n1 = 2 * d + 1
    # polynomial as dict: exponent tuple -> coeff
    poly = {tuple([0] * n1): 1}
    def mul(P, Qd):
        R = {}
        for e1, c1 in P.items():
            for e2, c2 in Qd.items():
                e = tuple((x + y) % m for x, y in zip(e1, e2))
                R[e] = R.get(e, 0) + c1 * c2
        return {e: c for e, c in R.items() if c != 0}
    def var_poly(i, power):  # t_i^power, i in 1..n1
        e = [0] * n1
        e[i - 1] = power % m
        return {tuple(e): 1}
    def lin_minus_one(i):  # t_i - 1
        P = dict(var_poly(i, 1))
        z = tuple([0] * n1)
        P[z] = P.get(z, 0) - 1
        return {e: c for e, c in P.items() if c != 0}
    def phi_prod(j, k):  # phi(t_j t_k) = sum_{u=0}^{m-1} (t_j t_k)^u
        P = {}
        for u in range(m):
            e = [0] * n1
            e[j - 1] = u % m
            e[k - 1] = u % m
            P[tuple(e)] = P.get(tuple(e), 0) + 1
        return P
    for i, (j, k) in enumerate(J):
        poly = mul(poly, lin_minus_one(k))          # tau_J factor (t_{k_i} - 1), including i = 0
        if i >= 1:
            poly = mul(poly, phi_prod(j, k))        # phi(t_{j_i} t_{k_i}) for i >= 1 (j_0 = 0 excluded)
    return poly

def rref_mod_p(M, p):
    """Return (basis rows in RREF, pivot cols) of the row space of M mod p.  M int64 array."""
    M = M.copy() % p
    rows, cols = M.shape
    pivs = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        i = r + nz[0]
        if i != r:
            M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        others = np.nonzero(M[:, c])[0]
        others = others[others != r]
        if others.size:
            M[others] = (M[others] - np.outer(M[others, c], M[r])) % p
        pivs.append(c)
        r += 1
    return M[:r], pivs

class IncrementalRank:
    def __init__(self, ncols, p):
        self.p = p
        self.B = np.zeros((0, ncols), dtype=np.int64)
        self.pivs = []
    def add(self, rows):
        p = self.p
        rows = rows % p
        if self.B.shape[0]:
            rows = (rows - rows[:, self.pivs] @ self.B) % p
        # drop zero rows
        nzr = np.nonzero(rows.any(axis=1))[0]
        if nzr.size == 0:
            return
        rows = rows[nzr]
        newB, newp = rref_mod_p(rows, p)
        if not newp:
            return
        # reduce old basis at the new pivots
        if self.B.shape[0]:
            self.B = (self.B - self.B[:, newp] @ newB) % p
        self.B = np.vstack([self.B, newB])
        self.pivs = self.pivs + newp
        # keep RREF ordering irrelevant; we only need B[i, pivs[j]] = delta_ij, which holds
    def rank(self):
        return self.B.shape[0]

def ideal_dim_literal(m, d, K, p, chunk=128):
    n1 = 2 * d + 1
    D = m ** n1
    # all exponent tuples, index = mixed radix (base m), position 0 most significant
    E = np.array(list(itertools.product(range(m), repeat=n1)), dtype=np.int64)  # D x n1
    w = np.array([m ** (n1 - 1 - i) for i in range(n1)], dtype=np.int64)
    IR = IncrementalRank(D, p)
    for J in K:
        poly = build_psi_vec(m, d, J)
        v = np.zeros(D, dtype=np.int64)
        for e, c in poly.items():
            v[int(np.dot(np.array(e), w))] = c % p
        # translates: row(mu)[nu] = v[nu - mu]
        for start in range(0, D, chunk):
            mus = E[start:start + chunk]  # c x n1
            # index of (nu - mu) for all nu, mu: (c, D)
            idx = (((E[None, :, :] - mus[:, None, :]) % m) * w).sum(axis=2)
            rows = v[idx]
            IR.add(rows)
    return IR.rank()

# ---------- (C) pair factor ----------
def pair_factor_dim(m, p):
    D = m * m
    E = np.array(list(itertools.product(range(m), repeat=2)), dtype=np.int64)
    w = np.array([m, 1], dtype=np.int64)
    # g = (t_b - 1) phi(t_a t_b), a = index 1, b = index 2
    poly = {}
    for u in range(m):
        for (eb, c) in [((u + 1) % m, 1), (u % m, -1)]:
            e = (u % m, eb)
            poly[e] = poly.get(e, 0) + c
    v = np.zeros(D, dtype=np.int64)
    for e, c in poly.items():
        v[e[0] * m + e[1]] = c % p
    idx = (((E[None, :, :] - E[:, None, :]) % m) * w).sum(axis=2)
    rows = v[idx]
    B, pv = rref_mod_p(rows, p)
    return len(pv)

# ---------- (D) factorisation over Z ----------
def check_factorisation(m, d, s):
    """psi_J == psi_{J'} * prod_{i>s} (t_{2i+1}-1) phi(t_{2i} t_{2i+1}) as exact polynomials in Z[t]/(t^m-1)."""
    n1 = 2 * d + 1
    K = J_sd(s, d)
    Jp_list = J_of(s)
    assert len(K) == len(Jp_list) == dfact(2 * s + 1)
    ok = True
    for Jp in Jp_list:
        J = Jp + [[2 * i, 2 * i + 1] for i in range(s + 1, d + 1)]
        # DS ordering check: j_i < k_i, j_0 < j_1 < ...
        assert all(a < b for a, b in J) and all(J[i][0] < J[i + 1][0] for i in range(len(J) - 1))
        assert J in K
        psi_J = build_psi_vec(m, d, J)
        # psi_{J'} embedded in n1 variables
        psi_Jp_small = build_psi_vec(m, s, Jp)
        psi_Jp = {tuple(list(e) + [0] * (n1 - (2 * s + 1))): c for e, c in psi_Jp_small.items()}
        prod = psi_Jp
        for i in range(s + 1, d + 1):
            a, b = 2 * i, 2 * i + 1
            g = {}
            for u in range(m):
                for (eb, c) in [((u + 1) % m, 1), (u % m, -1)]:
                    e = [0] * n1
                    e[a - 1] = u % m
                    e[b - 1] = eb
                    g[tuple(e)] = g.get(tuple(e), 0) + c
            new = {}
            for e1, c1 in prod.items():
                for e2, c2 in g.items():
                    e = tuple((x + y) % m for x, y in zip(e1, e2))
                    new[e] = new.get(e, 0) + c1 * c2
            prod = {e: c for e, c in new.items() if c != 0}
        if prod != psi_J:
            ok = False
    return ok

def primes_of(m):
    ps, x, q = [], m, 2
    while q * q <= x:
        if x % q == 0:
            ps.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        ps.append(x)
    return ps

# ---------- main ----------
print("Q_k(m) table:")
for m in (3, 5, 7, 9):
    print("  m=%d:" % m, [Q(k, m) for k in range(0, 5)])
print()

print("(D) factorisation psi_J = psi_{J'} * prod g_i (exact over Z):")
for (m, d, s) in [(3, 2, 0), (3, 2, 1), (3, 3, 1), (5, 2, 0), (5, 2, 1), (5, 3, 2), (9, 2, 1)]:
    print("  (m,d,s)=(%d,%d,%d): %s" % (m, d, s, check_factorisation(m, d, s)))
print()

print("(C) pair factor dim (t_b-1)phi(t_a t_b) in F_p[t_a,t_b]/(t^m-1), expected m-1:")
for m in (3, 5, 7, 9, 15):
    for p in primes_of(m):
        print("  m=%d p=%d: dim=%d (m-1=%d)" % (m, p, pair_factor_dim(m, p), m - 1))
print()

print("(A) |Gamma_K| for K=J(s,d) by Definition 1.3 vs Q_s(m)(m-1)^{d-s}:")
cellsA = [(m, d, s) for m in (3, 5) for d in range(0, 4) for s in range(0, d + 1)] + \
         [(7, d, s) for d in range(0, 3) for s in range(0, d + 1)]
for (m, d, s) in cellsA:
    K = J_sd(s, d)
    assert len(K) == dfact(2 * s + 1)
    t0 = time.time()
    g = gamma_K_count(m, d, K)
    pred = Q(s, m) * (m - 1) ** (d - s)
    print("  (m,d,s)=(%d,%d,%d): |K|=%d |Gamma_K|=%d predicted=%d %s [%.1fs]" %
          (m, d, s, len(K), g, pred, "OK" if g == pred else "MISMATCH", time.time() - t0))
print()

print("(B) literal ideal dimension dim_{F_p}(psi_J : J in K) vs |Gamma_K| (equality <=> torsion free):")
cellsB = [(3, 1, 0), (3, 1, 1), (3, 2, 0), (3, 2, 1), (3, 2, 2), (3, 3, 0), (3, 3, 1), (3, 3, 2),
          (5, 1, 0), (5, 1, 1), (9, 1, 0), (9, 1, 1), (7, 1, 1), (5, 2, 0), (5, 2, 1)]
for (m, d, s) in cellsB:
    K = J_sd(s, d)
    pred = Q(s, m) * (m - 1) ** (d - s)
    for p in primes_of(m):
        t0 = time.time()
        dim = ideal_dim_literal(m, d, K, p)
        print("  (m,d,s)=(%d,%d,%d) p=%d: |K|=%d dim=%d |Gamma_K|=%d quotient=%d %s [%.1fs]" %
              (m, d, s, p, len(K), dim, pred, m ** (2 * d + 1) - dim, "OK" if dim == pred else "MISMATCH",
               time.time() - t0))
        sys.stdout.flush()
print()
print("total wall %.1fs" % (time.time() - t_start))
