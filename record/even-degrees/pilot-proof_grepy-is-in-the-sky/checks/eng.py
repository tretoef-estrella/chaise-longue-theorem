# eng.py — the pilot's own engine («Grepy is in the Sky», 2 Oct 2026).
# Written from scratch; it does not import the auditor's rooftop engines.
#
# Box rings  F_p[y_1..y_n]/(y_i^{b_i})  and graded linear algebra in them.
#   * a homogeneous polynomial is a pair (E, c): E an integer array (T, n) of exponent vectors, c an array (T,) of coefficients
#   * linear algebra is done degree by degree; inside one degree the monomials are put in a chosen order
#     and a subspace is kept as an echelon basis with pairwise distinct leading monomials («pivots»)
#   * p = 2: vectors are Python integers used as bit sets (highest bit = first monomial of the order)
#   * p odd: dense numpy rows, reduced row echelon form (own elimination; python-flint only as a cross-check)
import itertools
import numpy as np
from fractions import Fraction
from math import factorial


# ---------------------------------------------------------------- combinatorics
def matchings(points):
    """All perfect matchings of the list `points` (even length), as lists of pairs (a, b) with a < b."""
    points = list(points)
    if not points:
        return [[]]
    a, rest = points[0], points[1:]
    out = []
    for i, b in enumerate(rest):
        for M in matchings(rest[:i] + rest[i + 1:]):
            out.append([(a, b)] + M)
    return out


def egf_coeff(series_list, n):
    """n! [x^n] of the product of the given power series (lists of Fractions, index = power)."""
    acc = [Fraction(1)] + [Fraction(0)] * n
    for s in series_list:
        new = [Fraction(0)] * (n + 1)
        for i, a in enumerate(acc):
            if a:
                for j in range(0, n + 1 - i):
                    if s[j]:
                        new[i + j] += a * s[j]
        acc = new
    return int(acc[n] * factorial(n))


def series_I0(n):      # I_0(2x) = sum x^(2b)/(b!)^2
    return [Fraction(1, factorial(i // 2) ** 2) if i % 2 == 0 else Fraction(0) for i in range(n + 1)]


def series_cosh(n):
    return [Fraction(1, factorial(i)) if i % 2 == 0 else Fraction(0) for i in range(n + 1)]


def N_odd(r, n):
    """N_r(n) = n! [x^n] cosh(x) I_0(2x)^((r-1)/2)  (r odd): closed n-tuples, involution with one fixed point."""
    assert r % 2 == 1
    return egf_coeff([series_cosh(n)] + [series_I0(n)] * ((r - 1) // 2), n)


def Q_free(h, n):
    """n! [x^n] I_0(2x)^h : closed n-tuples for a fixed-point-free involution with h classes."""
    return egf_coeff([series_I0(n)] * h, n)


def closed_tuples_bruteforce(r, n):
    """Number of n-tuples in Z/r whose multiset is closed under negation, the fixed values used an even number of times."""
    cnt = 0
    for a in itertools.product(range(r), repeat=n):
        mult = [0] * r
        for x in a:
            mult[x] += 1
        ok = True
        for x in range(r):
            y = (-x) % r
            if x == y:
                if mult[x] % 2:
                    ok = False; break
            elif mult[x] != mult[y]:
                ok = False; break
        cnt += ok
    return cnt


# ---------------------------------------------------------------- the box ring
class Box:
    def __init__(self, sizes, p):
        self.sizes = tuple(int(b) for b in sizes)
        self.n = len(self.sizes)
        self.p = p
        self.maxdeg = sum(b - 1 for b in self.sizes)

    # ---- polynomials
    def one(self):
        return (np.zeros((1, self.n), dtype=np.int64), np.ones(1, dtype=np.int64))

    def clean(self, E, c):
        """Reduce modulo the box and modulo p, merge equal monomials."""
        c = c % self.p
        keep = (c != 0) & np.all(E < np.array(self.sizes), axis=1)
        E, c = E[keep], c[keep]
        if len(c) == 0:
            return (np.zeros((0, self.n), dtype=np.int64), np.zeros(0, dtype=np.int64))
        key = np.zeros(len(c), dtype=np.int64)
        for i in range(self.n):
            key = key * self.sizes[i] + E[:, i]
        order = np.argsort(key, kind='stable')
        key, E, c = key[order], E[order], c[order]
        uniq, start = np.unique(key, return_index=True)
        csum = np.add.reduceat(c, start) % self.p
        E = E[start]
        keep = csum != 0
        return (E[keep], csum[keep])

    def mul(self, f, g):
        (E1, c1), (E2, c2) = f, g
        if len(c1) == 0 or len(c2) == 0:
            return self.clean(np.zeros((0, self.n), dtype=np.int64), np.zeros(0, dtype=np.int64))
        E = (E1[:, None, :] + E2[None, :, :]).reshape(-1, self.n)
        c = (c1[:, None] * c2[None, :]).reshape(-1)
        return self.clean(E, c)

    def add(self, f, g, sg=1):
        return self.clean(np.concatenate([f[0], g[0]]), np.concatenate([f[1], sg * g[1]]))

    def poly(self, terms):
        """terms: iterable of (coefficient, {variable index: exponent})."""
        E, c = [], []
        for co, mon in terms:
            e = [0] * self.n
            for v, a in mon.items():
                e[v] += a
            E.append(e); c.append(co)
        return self.clean(np.array(E, dtype=np.int64).reshape(-1, self.n), np.array(c, dtype=np.int64))

    def var(self, i, a=1):
        return self.poly([(1, {i: a})])

    def shift(self, f, beta):
        """Multiply by the monomial y^beta."""
        E, c = f
        E2 = E + np.array(beta, dtype=np.int64)
        keep = np.all(E2 < np.array(self.sizes), axis=1)
        return (E2[keep], c[keep])

    def degree_parts(self, f):
        E, c = f
        d = E.sum(axis=1)
        return {int(k): (E[d == k], c[d == k]) for k in np.unique(d)}


def Dpoly(box, a, b, r, signed=True):
    """D_r(y_a, y_b) = sum_{u=0}^{r-1} (-1)^u y_a^u y_b^(r-1-u)   (signed=False: all coefficients 1)."""
    return box.poly([(((-1) ** u if signed else 1), {a: u, b: r - 1 - u}) for u in range(r)])


def prod(box, polys):
    f = box.one()
    for g in polys:
        f = box.mul(f, g)
    return f


# ---------------------------------------------------------------- graded spaces
class Graded:
    """A graded subspace of a box ring, kept degree by degree as an echelon basis.
    `key(E)` gives the sort key of the monomials inside one degree: the pivot of a vector is its FIRST monomial in that order."""

    def __init__(self, box, key=None):
        self.box = box
        self.key = key
        self.cols = {}      # degree -> (E_sorted (L, n), dict flat -> position)
        self.rows = {}      # degree -> p == 2: dict pivot_pos -> int ; p odd: (matrix, pivots)
        self._flatw = None

    def _flat(self, E):
        key = np.zeros(len(E), dtype=np.int64)
        for i in range(self.box.n):
            key = key * self.box.sizes[i] + E[:, i]
        return key

    def columns(self, d):
        if d not in self.cols:
            E = monomials_of_degree(self.box.sizes, d)
            if self.key is not None and len(E):
                k = self.key(E)
                order = np.lexsort(tuple(k[::-1])) if isinstance(k, (list, tuple)) else np.argsort(k, kind='stable')
                E = E[order]
            flat = self._flat(E)
            self.cols[d] = (E, {int(f): i for i, f in enumerate(flat)}, flat)
        return self.cols[d]

    def L(self, d):
        return len(self.columns(d)[0])

    def _rank(self):
        """rank[flat] = position of the monomial inside its degree (for the chosen order)."""
        if self._flatw is None:
            size = int(np.prod(self.box.sizes)) if self.box.n else 1
            rk = np.full(size, -1, dtype=np.int64)
            for d in range(self.box.maxdeg + 1):
                E, _, flat = self.columns(d)
                rk[flat] = np.arange(len(flat))
            self._flatw = rk
        return self._flatw

    def to_vec(self, d, f):
        """Homogeneous polynomial of degree d -> vector."""
        E, c = f
        L = self.L(d)
        pos = self._rank()[self._flat(E)] if len(c) else np.zeros(0, dtype=np.int64)
        if self.box.p == 2:
            bits = np.zeros(L, dtype=np.uint8)
            np.bitwise_xor.at(bits, pos, 1)
            return int.from_bytes(np.packbits(bits).tobytes(), 'big') >> ((-L) % 8)
        v = np.zeros(L, dtype=np.int64)
        np.add.at(v, pos, c)
        return (v % self.box.p).astype(np.int16 if self.box.p <= 181 else np.int64)

    def to_poly(self, d, v):
        E, _, _ = self.columns(d)
        L = len(E)
        if self.box.p == 2:
            idx = [L - 1 - i for i in range(L) if (v >> i) & 1]
            idx.sort()
            return (E[idx], np.ones(len(idx), dtype=np.int64))
        nz = np.flatnonzero(v)
        return (E[nz], v[nz].astype(np.int64))

    # ---- adding vectors
    def add_poly(self, f):
        for d, part in self.box.degree_parts(f).items():
            self.add_vecs(d, [self.to_vec(d, part)])

    def add_vecs(self, d, vecs):
        if self.box.p == 2:
            basis = self.rows.setdefault(d, {})
            for v in vecs:
                while v:
                    h = v.bit_length() - 1
                    b = basis.get(h)
                    if b is None:
                        basis[h] = v
                        break
                    v ^= b
        else:
            vecs = [v for v in vecs]
            if not vecs:
                self.rows.setdefault(d, (np.zeros((0, self.L(d)), dtype=np.int64), []))
                return
            old = self.rows.get(d)
            M = np.array(vecs).reshape(len(vecs), -1)
            if old is not None and len(old[0]):
                M = np.concatenate([old[0], M])
            self.rows[d] = rref_mod_p(M, self.box.p)

    def dim(self, d=None):
        if d is None:
            return sum(self.dim(e) for e in self.rows)
        if d not in self.rows:
            return 0
        return len(self.rows[d]) if self.box.p == 2 else len(self.rows[d][1])

    def hf(self):
        return {d: self.dim(d) for d in sorted(self.rows) if self.dim(d)}

    def pivots(self, d):
        """Positions (in the column order of degree d) of the pivots."""
        if d not in self.rows:
            return []
        L = self.L(d)
        if self.box.p == 2:
            return sorted(L - 1 - h for h in self.rows[d])
        return list(self.rows[d][1])

    def basis_polys(self, d):
        if d not in self.rows:
            return []
        if self.box.p == 2:
            return [self.to_poly(d, v) for v in self.rows[d].values()]
        return [self.to_poly(d, v) for v in self.rows[d][0]]

    def basis_vecs(self, d):
        if d not in self.rows:
            return []
        if self.box.p == 2:
            return list(self.rows[d].values())
        return list(self.rows[d][0])

    def contains_vec(self, d, v):
        if self.box.p == 2:
            basis = self.rows.get(d, {})
            while v:
                h = v.bit_length() - 1
                b = basis.get(h)
                if b is None:
                    return False
                v ^= b
            return True
        if d not in self.rows or len(self.rows[d][1]) == 0:
            return not np.any(v % self.box.p)
        M, piv = self.rows[d]
        v = v.astype(np.int64) % self.box.p
        for row, c in zip(M, piv):
            if v[c]:
                v = (v - v[c] * row.astype(np.int64)) % self.box.p
        return not np.any(v)

    def contains_poly(self, f):
        return all(self.contains_vec(d, self.to_vec(d, part)) for d, part in self.box.degree_parts(f).items())

    def contains_space(self, other):
        """other: Graded on the same box (any column order)."""
        for d in other.rows:
            for f in other.basis_polys(d):
                if not self.contains_vec(d, self.to_vec(d, f)):
                    return False
        return True


def rref_mod_p(M, p):
    """Reduced row echelon form modulo an odd prime p (own elimination). Returns (matrix of the non-zero rows, pivot columns).
    Storage: int16 when p <= 181 (all intermediate values stay below 2^15 in absolute value), int64 otherwise."""
    dt = np.int16 if p <= 181 else np.int64
    M = (M % p).astype(dt)
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.flatnonzero(M[r:, c])
        if nz.size == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        if inv != 1:
            M[r] = (M[r] * dt(inv)) % p
        col = M[:, c].copy()
        col[r] = 0
        idx = np.flatnonzero(col)
        if idx.size:
            M[idx] = (M[idx] - np.outer(col[idx], M[r])) % p
        piv.append(c)
        r += 1
    return (M[:r].copy(), piv)


_mono_cache = {}


def monomials_of_degree(sizes, d):
    """All exponent vectors e with 0 <= e_i < sizes[i] and sum d, as an array (L, n), in lexicographic order."""
    keyc = (tuple(sizes), d)
    if keyc in _mono_cache:
        return _mono_cache[keyc]
    n = len(sizes)
    if n == 0:
        out = np.zeros((1 if d == 0 else 0, 0), dtype=np.int64)
    else:
        parts = []
        rest_max = sum(b - 1 for b in sizes[1:])
        for e in range(min(sizes[0] - 1, d) + 1):
            if d - e > rest_max:
                continue
            sub = monomials_of_degree(sizes[1:], d - e)
            if len(sub):
                parts.append(np.concatenate([np.full((len(sub), 1), e, dtype=np.int64), sub], axis=1))
        out = np.concatenate(parts) if parts else np.zeros((0, n), dtype=np.int64)
    _mono_cache[keyc] = out
    return out


# ---------------------------------------------------------------- ideals
def ideal_from_generators(box, gens, key=None, free=None, verbose=False):
    """The ideal generated by the homogeneous polynomials `gens`, as a Graded space.
    free[i] (optional): list of variables whose monomials suffice as multipliers of gens[i]
    (to be used only when the other variables act on gens[i] through these, e.g. y_a D = -y_b D)."""
    S = Graded(box, key)
    for gi, g in enumerate(gens):
        if len(g[1]) == 0:
            continue
        d0 = int(g[0][0].sum())
        vs = list(range(box.n)) if free is None else list(free[gi])
        sub_sizes = [box.sizes[v] for v in vs]
        for e in range(0, sum(b - 1 for b in sub_sizes) + 1):
            if d0 + e > box.maxdeg:
                break
            mons = monomials_of_degree(tuple(sub_sizes), e)
            vecs = []
            for mrow in mons:
                beta = np.zeros(box.n, dtype=np.int64)
                beta[vs] = mrow
                h = box.shift(g, beta)
                if len(h[1]):
                    vecs.append(S.to_vec(d0 + e, h))
            if vecs:
                S.add_vecs(d0 + e, vecs)
    return S


def reorder(S, key):
    """The same graded space with another monomial order."""
    T = Graded(S.box, key)
    for d in S.rows:
        vecs = [T.to_vec(d, f) for f in S.basis_polys(d)]
        if vecs:
            T.add_vecs(d, vecs)
    return T


def slices(S, var=0):
    """Peel the variable `var` of the homogeneous ideal S of a box ring.
    Returns (box', [W_0, ..., W_{b-1}]) with W_j = {[y^j] f : f in S, deg_y f <= j} as Graded spaces of the box without `var`."""
    box = S.box
    b = box.sizes[var]
    key = lambda E: -E[:, var]            # highest exponent of y_var first
    T = reorder(S, key)
    sizes2 = box.sizes[:var] + box.sizes[var + 1:]
    box2 = Box(sizes2, box.p)
    W = [Graded(box2) for _ in range(b)]
    for d in T.rows:
        E, _, _ = T.columns(d)
        for f in T.basis_polys(d):
            # the pivot is the first monomial of f in the order: f is stored sorted by position
            j = int(f[0][:, var].max())
            sel = f[0][:, var] == j
            g = (np.delete(f[0][sel], var, axis=1), f[1][sel])
            W[j].add_vecs(d - j, [W[j].to_vec(d - j, g)])
    return box2, W
