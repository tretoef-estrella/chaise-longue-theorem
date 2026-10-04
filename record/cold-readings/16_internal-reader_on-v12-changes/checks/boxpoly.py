# boxpoly.py — sparse polynomials in y_1..y_n over Z or F_p, truncated to the box (y_i^r), and a graded
# ideal-membership test by linear algebra (python-flint nmod_mat / fmpz_mat).  Grepy Lupa's own code.
import itertools
from flint import nmod_mat, fmpz_mat

class BP:
    __slots__ = ('d', 'n', 'r', 'p')
    def __init__(self, d, n, r, p):
        self.d = d; self.n = n; self.r = r; self.p = p
    @staticmethod
    def zero(n, r, p): return BP({}, n, r, p)
    @staticmethod
    def one(n, r, p): return BP({(0,)*n: 1}, n, r, p)
    @staticmethod
    def var_pow(i, e, n, r, p, c=1):
        if e >= r: return BP({}, n, r, p)
        ex = [0]*n; ex[i] = e
        return BP(BP._norm({tuple(ex): c}, p), n, r, p)
    @staticmethod
    def _norm(d, p):
        if p:
            return {k: v % p for k, v in d.items() if v % p}
        return {k: v for k, v in d.items() if v}
    def __add__(self, o):
        d = dict(self.d)
        for k, v in o.d.items(): d[k] = d.get(k, 0) + v
        return BP(BP._norm(d, self.p), self.n, self.r, self.p)
    def __neg__(self):
        return BP(BP._norm({k: -v for k, v in self.d.items()}, self.p), self.n, self.r, self.p)
    def __sub__(self, o): return self + (-o)
    def __mul__(self, o):
        if isinstance(o, int):
            return BP(BP._norm({k: v*o for k, v in self.d.items()}, self.p), self.n, self.r, self.p)
        d = {}; r = self.r
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(a+b for a, b in zip(k1, k2))
                if max(k) < r:
                    d[k] = d.get(k, 0) + v1*v2
        return BP(BP._norm(d, self.p), self.n, self.r, self.p)
    __rmul__ = __mul__
    def is_zero(self): return not self.d
    def degrees(self): return {sum(k) for k in self.d}

def y(i, n, r, p): return BP.var_pow(i, 1, n, r, p)

def Dminus(i, j, n, r, p):
    # D^-(y_i, y_j) = sum_{u=0}^{r-2} (-1)^u y_i^u y_j^{r-2-u}
    tot = BP.zero(n, r, p)
    for u in range(r-1):
        tot = tot + BP.var_pow(i, u, n, r, p) * BP.var_pow(j, r-2-u, n, r, p) * ((-1)**u)
    return tot
def Dplus(i, j, n, r, p):
    tot = BP.zero(n, r, p)
    for u in range(r):
        tot = tot + BP.var_pow(i, u, n, r, p) * BP.var_pow(j, r-1-u, n, r, p) * ((-1)**u)
    return tot
def vandermonde(S, n, r, p):
    tot = BP.one(n, r, p)
    S = sorted(S)
    for a in range(len(S)):
        for b in range(a+1, len(S)):
            tot = tot * (y(S[b], n, r, p) - y(S[a], n, r, p))
    return tot

def box_monomials(n, r, deg):
    out = []
    def rec(i, left, cur):
        if i == n:
            if left == 0: out.append(tuple(cur))
            return
        for e in range(min(r-1, left)+1):
            cur.append(e); rec(i+1, left-e, cur); cur.pop()
    rec(0, deg, [])
    return out

def member(f, gens, n, r, p):
    """graded membership of the homogeneous f in the ideal (gens) + (y_i^r) of F_p[y] (p prime) or Q[y] (p=0).
    Returns (is_member, f_is_zero)."""
    if f.is_zero():
        return True, True
    degs = f.degrees(); assert len(degs) == 1, 'f not homogeneous'
    d = degs.pop()
    cols = box_monomials(n, r, d); ci = {m: k for k, m in enumerate(cols)}
    rows = []
    for g in gens:
        if g.is_zero(): continue
        gd = g.degrees(); assert len(gd) == 1, 'generator not homogeneous'
        e = d - gd.pop()
        if e < 0: continue
        for m in box_monomials(n, r, e):
            mono = BP({m: 1}, n, r, p)
            h = g * mono
            if h.is_zero(): continue
            v = [0]*len(cols)
            for k, c in h.d.items(): v[ci[k]] = c
            rows.append(v)
    fv = [0]*len(cols)
    for k, c in f.d.items(): fv[ci[k]] = c
    if not rows:
        return False, False
    if p:
        M1 = nmod_mat(rows, p); M2 = nmod_mat(rows + [fv], p)
    else:
        M1 = fmpz_mat(rows); M2 = fmpz_mat(rows + [fv])
    return M1.rank() == M2.rank(), False
