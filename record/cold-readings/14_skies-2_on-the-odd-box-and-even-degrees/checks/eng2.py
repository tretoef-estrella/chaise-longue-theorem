# eng2.py -- Grepy Skies 2 (cold reader). My own engine, written from the definitions in
# PROOF_ODD_BOX.md / the paper; no code of the target is available or used.
# Box ring Z[y_1..y_n]/(y_i^r): polynomials are dicts {exponent tuple: integer coefficient}.
# Ideals are homogeneous; dimensions are computed degree by degree over F_p with python-flint.
import itertools, sys
from flint import nmod_mat

# ---------------------------------------------------------------- polynomials over Z, box r
def padd(a, b, s=1):
    c = dict(a)
    for k, v in b.items():
        w = c.get(k, 0) + s * v
        if w: c[k] = w
        else: c.pop(k, None)
    return c

def pmul(a, b, r):
    c = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            if max(k) >= r: continue
            w = c.get(k, 0) + va * vb
            if w: c[k] = w
            else: c.pop(k, None)
    return c

def pscal(a, s):
    return {k: s * v for k, v in a.items()} if s else {}

def one(n): return {tuple([0] * n): 1}

def mono(n, i, e, r):
    if e >= r: return {}
    k = [0] * n; k[i] = e
    return {tuple(k): 1}

def Dpoly(n, a, b, r, R=None):
    """D_R(y_a,y_b) = sum_{u=0}^{R-1} (-1)^u y_a^u y_b^{R-1-u}; default R=r (the D of Theorem O)."""
    if R is None: R = r
    c = {}
    for u in range(R):
        k = [0] * n; k[a] += u; k[b] += R - 1 - u
        if max(k) >= r: continue
        c[tuple(k)] = (-1) ** u
    return c

def Bpoly(n, a, b, r):
    """B(y_a,y_b) = D_{r-1}(y_a,y_b) = sum_{u=0}^{r-2} (-1)^u y_a^u y_b^{r-2-u}."""
    return Dpoly(n, a, b, r, R=r - 1)

def vdm(n, blk, r):
    """Vandermonde prod_{c<c'} (y_{b_c'} - y_{b_c}) for the sorted block."""
    blk = sorted(blk)
    f = one(n)
    for i in range(len(blk)):
        for j in range(i + 1, len(blk)):
            f = pmul(f, padd(mono(n, blk[j], 1, r), mono(n, blk[i], 1, r), -1), r)
            if not f: return f
    return f

def pfaffian(idx, entry, n, r):
    """Pfaffian of the alternating matrix with entries entry(i,j) (i before j in idx), polynomials."""
    if not idx: return one(n)
    if len(idx) % 2: return {}
    i = idx[0]; rest = idx[1:]
    tot = {}
    for pos, j in enumerate(rest):
        e = entry(i, j)
        if not e: continue
        sub = pfaffian(rest[:pos] + rest[pos + 1:], entry, n, r)
        if not sub: continue
        tot = padd(tot, pmul(e, sub, r), (-1) ** pos)
    return tot

def bordered_pf(n, N, E, r, extra_cols=()):
    """Pf(N; y^{e_1},...,y^{e_s}, extra...) of Section 3: indices N (variables, in the given order),
    then borders. Entry between two variables i<j (in the order of N): B(y_i,y_j); between variable i
    and border k: c_k(i); between borders: 0. extra_cols: functions i -> polynomial."""
    N = list(N); E = sorted(E)
    cols = [(lambda i, e=e: mono(n, i, e, r)) for e in E] + list(extra_cols)
    idx = [('v', i) for i in N] + [('b', k) for k in range(len(cols))]
    def entry(a, b):
        if a[0] == 'v' and b[0] == 'v': return Bpoly(n, a[1], b[1], r)
        if a[0] == 'v' and b[0] == 'b': return cols[b[1]](a[1])
        return {}
    return pfaffian(idx, entry, n, r)

def E_l(l, r):
    return [r - 1] if l == 0 else list(range(l - 1))

def normal(f):
    """canonical form up to sign (for de-duplication)."""
    if not f: return None
    k0 = min(f)
    s = 1 if f[k0] > 0 else -1
    return tuple(sorted((k, s * v) for k, v in f.items()))

# ---------------------------------------------------------------- linear algebra over F_p, graded
_mono_cache = {}
def monos(n, r, d):
    key = (n, r, d)
    if key not in _mono_cache:
        out = []
        def rec(i, left, cur):
            if i == n:
                if left == 0: out.append(tuple(cur))
                return
            for e in range(min(r - 1, left), -1, -1):   # y_1-exponent DESCENDING first
                cur.append(e); rec(i + 1, left - e, cur); cur.pop()
        rec(0, d, [])
        _mono_cache[key] = (out, {m: i for i, m in enumerate(out)})
    return _mono_cache[key]

def rref_rows(rows, n, r, d, p):
    """rows: list of dicts {exp: coeff}. returns list of dicts (rref basis), pivots (exps).
    Column order: lexicographic with exponents descending, y_1 first (so y_1-exponent descending)."""
    ml, mi = monos(n, r, d)
    rows = [x for x in rows if x]
    if not rows or not ml: return [], []
    nc = len(ml)
    ent = [0] * (len(rows) * nc)
    for a, row in enumerate(rows):
        base = a * nc
        for k, v in row.items():
            ent[base + mi[k]] = v % p
    M = nmod_mat(len(rows), nc, ent, p)
    Rm, rk = M.rref()
    out = []; piv = []
    for a in range(rk):
        row = {}
        first = None
        for c in range(nc):
            v = int(Rm[a, c])
            if v:
                if first is None: first = c
                row[ml[c]] = v
        out.append(row); piv.append(ml[first])
    return out, piv

def deg(f):
    for k in f: return sum(k)
    return None

def is_homog(f):
    ds = {sum(k) for k in f}
    return len(ds) <= 1

def ideal(gens, n, r, p, maxdeg=None):
    """graded basis of the ideal generated by homogeneous gens (dict polys over Z) in F_p[y]/(y^r).
    returns {d: (rows, pivots)}; if maxdeg is given, only the degrees <= maxdeg are computed."""
    bydeg = {}
    for g in gens:
        g = {k: v % p for k, v in g.items() if v % p}
        if not g: continue
        assert is_homog(g)
        bydeg.setdefault(deg(g), []).append(g)
    res = {}
    prev = []
    top = n * (r - 1) if maxdeg is None else min(maxdeg, n * (r - 1))
    for d in range(0, top + 1):
        rows = list(bydeg.get(d, []))
        for b in prev:
            for i in range(n):
                nb = {}
                for k, v in b.items():
                    if k[i] + 1 < r:
                        kk = list(k); kk[i] += 1
                        nb[tuple(kk)] = v
                if nb: rows.append(nb)
        if rows:
            basis, piv = rref_rows(rows, n, r, d, p)
        else:
            basis, piv = [], []
        res[d] = (basis, piv)
        prev = basis
    return res

def idim(I): return sum(len(b) for b, _ in I.values())
def hilb(I): return [len(I[d][0]) for d in sorted(I) if len(I[d][0])]

def slices(I, n, r):
    """W_j(V) for j=0..r-1, peeling y_1 (variable index 0): {j: {e: [rows in n-1 vars]}} and dims.
    Uses: in the rref with y_1-exponent descending columns, the rows whose pivot has y_1-exponent j
    are in V_{<=j} and their y_1^j-coefficients are a basis of (W_j) in that degree."""
    W = {j: {} for j in range(r)}
    for d, (basis, piv) in I.items():
        for row, pv in zip(basis, piv):
            j = pv[0]
            assert max(k[0] for k in row) == j
            coeff = {k[1:]: v for k, v in row.items() if k[0] == j}
            W[j].setdefault(d - j, []).append(coeff)
    return W

def wdim(Wj): return sum(len(v) for v in Wj.values())

def contained(Vsmall, Wj, n1, r, p):
    """is the graded space Vsmall ({d: (rows,piv)}) contained in Wj ({e: rows})? (n1 variables)"""
    for d, (basis, _) in Vsmall.items():
        if not basis: continue
        w = Wj.get(d, [])
        b1, _ = rref_rows(list(w), n1, r, d, p)
        b2, _ = rref_rows(list(w) + list(basis), n1, r, d, p)
        if len(b2) != len(b1): return False
    return True

def member(f, I, n, r, p):
    """is the homogeneous polynomial f in the ideal I (graded basis)?"""
    f = {k: v % p for k, v in f.items() if v % p}
    if not f: return True
    d = deg(f)
    basis = I[d][0]
    b2, _ = rref_rows(list(basis) + [f], n, r, d, p)
    return len(b2) == len(basis)

# ---------------------------------------------------------------- partitions, shapes
def partitions(n, maxparts, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0: yield (); return
    if maxparts == 0: return
    for a in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - a, maxparts - 1, a):
            yield (a,) + rest

def Pset(n, h):
    """P_n = Par_n^{(h)}: partitions with <= h parts, size <= n, size = n mod 2."""
    if n < 0: return []
    out = []
    for s in range(n % 2, n + 1, 2):
        out.extend(partitions(s, h))
    return out

def Sh(m, h):
    return [(l, 0) for l in Pset(m, h)] + [(l, 1) for l in Pset(m - 1, h)]

def S(l, t): return sum(l[:t])
def wleq(a, b):
    L = max(len(a), len(b))
    return all(S(a, t) <= S(b, t) for t in range(1, L + 1))

def minus(l, j):
    x = list(l); x[j] -= 1
    return tuple(sorted([v for v in x if v > 0], reverse=True))
def plus(l, j):
    x = list(l); x[j] += 1
    return tuple(sorted(x, reverse=True))
def join1(l): return tuple(l) + (1,)
def conj(l):
    return [sum(1 for v in l if v > c) for c in range(l[0])] if l else []

def options(mu, eps, h):
    """Lemma 2.1: the r = 2h+1 shapes of (y, M') for a tail of shape (mu, eps), with multiplicity."""
    l = len(mu); out = []
    for j in range(l): out.append((minus(mu, j), eps))
    out.append((tuple(mu), 1 - eps))
    for _ in range(2 * (h - l)): out.append((join1(mu), eps))
    for j in reversed(range(l)): out.append((plus(mu, j), eps))
    assert len(out) == 2 * h + 1
    return out

def FL(Lam, mu, eps, h):
    return sum(1 for o in options(mu, eps, h) if o in Lam)

def is_interlaced(Lam, m, h):
    for eps in (0, 1):
        univ = Pset(m - eps, h)
        comp = {l for (l, e) in Lam if e == eps}
        for nu in comp:
            for ka in univ:
                if wleq(ka, nu) and ka not in comp: return False
    for (nu, eps) in Lam:
        for j in range(len(nu)):
            if (minus(nu, j), 1 - eps) not in Lam: return False
    return True

def is_pair_of_downsets(Lam, m, h):
    for eps in (0, 1):
        univ = Pset(m - eps, h)
        comp = {l for (l, e) in Lam if e == eps}
        for nu in comp:
            for ka in univ:
                if wleq(ka, nu) and ka not in comp: return False
    return True

def all_subsets(shapes):
    for bits in range(1 << len(shapes)):
        yield frozenset(s for i, s in enumerate(shapes) if bits >> i & 1)

def interlaced_pairs(m, h):
    sh = Sh(m, h)
    return [L for L in all_subsets(sh) if is_interlaced(L, m, h)]

def layer(Lam, m, h, i):
    return frozenset(s for s in Sh(m - 1, h) if FL(Lam, s[0], s[1], h) > i)

def shape_of_point(M, h):
    cnt = {}
    for v in M: cnt[v] = cnt.get(v, 0) + 1
    parts = []
    for u in range(1, h + 1):
        d = abs(cnt.get(u, 0) - cnt.get(-u, 0))
        if d: parts.append(d)
    return (tuple(sorted(parts, reverse=True)), cnt.get(0, 0) % 2)

def points(m, h):
    return itertools.product(range(-h, h + 1), repeat=m)

def Zcount(Lam, m, h):
    return sum(1 for M in points(m, h) if shape_of_point(M, h) in Lam)

# ---------------------------------------------------------------- patterns (Definition 4.1)
def matchings(items):
    items = list(items)
    if not items: yield (); return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]
        for rest in matchings(items[1:i] + items[i + 1:]):
            yield ((a, b),) + rest

def pair_sets(items, p):
    """all sets of p disjoint pairs inside items (as sorted tuples of pairs), with the rest."""
    items = list(items)
    for sub in itertools.combinations(items, 2 * p):
        rest = [x for x in items if x not in sub]
        for mt in matchings(sub):
            yield mt, rest

def block_splits(items, sizes):
    """ordered tuple of disjoint blocks with the given sizes, covering items; equal sizes that are
    adjacent in `sizes` are generated once (min elements increasing)."""
    items = list(items)
    if not sizes:
        if not items: yield ()
        return
    s = sizes[0]
    for blk in itertools.combinations(items, s):
        rest = [x for x in items if x not in blk]
        for more in block_splits(rest, sizes[1:]):
            if more and len(sizes) > 1 and sizes[1] == s and more[0] and blk and min(more[0]) < min(blk):
                continue
            yield (blk,) + more

def pattern_products(shape, I, n, r):
    """products (dict polys over Z, in n variables) of all the patterns of `shape` on the index list I
    (indices are 0-based variable indices). De-duplicated up to sign."""
    lam, eps = shape
    m = len(I); l = len(lam)
    cols = conj(lam)
    seen = set(); out = []
    def emit(f):
        key = normal(f)
        if key is None or key in seen: return
        seen.add(key); out.append(f)
    if eps == 0:
        p = (m - sum(lam))
        assert p % 2 == 0; p //= 2
        for P, rest in pair_sets(I, p):
            DP = one(n)
            for (a, b) in P: DP = pmul(DP, Dpoly(n, a, b, r), r)
            for blocks in block_splits(rest, cols):
                f = DP
                for blk in blocks:
                    f = pmul(f, vdm(n, blk, r), r)
                    if not f: break
                emit(f)
    else:
        tot = m - 1 - sum(lam)
        assert tot % 2 == 0 and tot >= 0
        E = E_l(l, r)
        for t in range(0, tot // 2 + 1):
            p = tot // 2 - t
            ms = l + 1 + 2 * t
            for Mb in itertools.combinations(I, ms):
                PF = bordered_pf(n, Mb, E, r)
                if not PF: continue
                rest0 = [x for x in I if x not in Mb]
                for P, rest in pair_sets(rest0, p):
                    DP = PF
                    for (a, b) in P: DP = pmul(DP, Dpoly(n, a, b, r), r)
                    for blocks in block_splits(rest, cols[1:]):
                        f = DP
                        for blk in blocks:
                            f = pmul(f, vdm(n, blk, r), r)
                            if not f: break
                        emit(f)
    return out

_pp_cache = {}
def pattern_products_cached(shape, I, n, r):
    key = (shape, tuple(I), n, r)
    if key not in _pp_cache: _pp_cache[key] = pattern_products(shape, I, n, r)
    return _pp_cache[key]

def V_gens(Lam, I, n, r):
    g = []
    for s in sorted(Lam):
        g.extend(pattern_products_cached(s, I, n, r))
    return g

def shname(s):
    return "(%s)%s" % (",".join(map(str, s[0])), "*" if s[1] else "")
def Lname(L):
    return "{" + " ".join(shname(s) for s in sorted(L, key=lambda s: (s[1], sum(s[0]), s[0]))) + "}"

def Nr(r, n):
    """N_r(n) = n! [x^n] cosh(x) I_0(2x)^{(r-1)/2}, by exact rational arithmetic."""
    from fractions import Fraction
    from math import factorial
    h = (r - 1) // 2
    cosh = [Fraction(1, factorial(i)) if i % 2 == 0 else Fraction(0) for i in range(n + 1)]
    I0 = [Fraction(1, factorial(i // 2) ** 2) if i % 2 == 0 else Fraction(0) for i in range(n + 1)]
    def mul(a, b):
        c = [Fraction(0)] * (n + 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i + j <= n and y: c[i + j] += x * y
        return c
    f = cosh
    for _ in range(h): f = mul(f, I0)
    v = f[n] * factorial(n)
    assert v.denominator == 1
    return int(v)
