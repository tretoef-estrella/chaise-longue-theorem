# grj.py — pilot. The ideal gr J(Z): top-degree forms of the functions on the grid T^m supported on a set Z of points.
# T = {0} U mu_{r-1} inside F_p (needs (r-1) | (p-1)); involution u -> -u, one fixed point 0.
# Functions on T^m = F_p[y_1..y_m]/(y_i^r - y_i); the delta function of a point is a product of Lagrange polynomials.
import itertools, numpy as np
from eng import Box, Graded, rref_mod_p
import shapes as sh

class Grid:
    def __init__(self, r, m, p):
        assert (p - 1) % (r - 1) == 0 and r % 2 == 1
        self.r, self.m, self.p = r, m, p
        h = (r - 1) // 2
        g = next(z for z in range(2, p) if len({pow(z, e, p) for e in range(1, p)}) == p - 1) if p > 3 else 2
        om = pow(g, (p - 1) // (r - 1), p)
        self.T = [0] + [pow(om, j, p) for j in range(r - 1)]          # index 0 is the fixed point; index 1+j <-> om^j ; -om^j = om^(j+h)
        self.neg = [0] + [1 + (j + h) % (r - 1) for j in range(r - 1)]
        # Lagrange polynomials: L[u] = coefficient vector (length r) of the polynomial that is 1 at T[u] and 0 elsewhere
        L = np.zeros((r, r), dtype=np.int64)
        for u in range(r):
            poly = [1]
            den = 1
            for w in range(r):
                if w == u: continue
                new = [0] * (len(poly) + 1)
                for i, c in enumerate(poly):
                    new[i + 1] = (new[i + 1] + c) % p
                    new[i] = (new[i] - c * self.T[w]) % p
                poly = new
                den = den * (self.T[u] - self.T[w]) % p
            inv = pow(den, p - 2, p)
            L[u] = [(c * inv) % p for c in poly]
        self.L = L
        # all points and their shapes
        self.points = list(itertools.product(range(r), repeat=m))
        self.shape = [self._shape(z) for z in self.points]
        self.box = Box([r] * m, p)
        # exponent vectors of the flat index (variable 0 most significant), and total degrees
        idx = np.arange(r ** m)
        self.E = np.stack([(idx // r ** (m - 1 - i)) % r for i in range(m)], axis=1) if m else np.zeros((1, 0), dtype=np.int64)
        self.deg = self.E.sum(axis=1)
        self.order = np.argsort(-self.deg, kind='stable')             # highest degree first

    def _shape(self, z):
        r = self.r; h = (r - 1) // 2
        mult = [0] * r
        for x in z: mult[x] += 1
        lam = [abs(mult[1 + j] - mult[1 + j + h]) for j in range(h)]
        return (sh.norm(lam), mult[0] % 2)

    def delta(self, z):
        v = np.ones(1, dtype=np.int64)
        for x in z:
            v = np.multiply.outer(v, self.L[x]).reshape(-1) % self.p
        return v

    def grJ(self, Lam):
        """Graded space of the top-degree forms of the functions supported on Z_Lam."""
        S = Graded(self.box)
        rows = [self.delta(z) for z, s in zip(self.points, self.shape) if s in Lam]
        if not rows:
            return S
        M = np.array(rows, dtype=np.int64)[:, self.order]
        M, piv = rref_mod_p(M, self.p)
        degs = self.deg[self.order]
        for row, c in zip(M, piv):
            d = int(degs[c])
            sel = np.flatnonzero((degs == d) & (row != 0))
            f = (self.E[self.order[sel]], row[sel].astype(np.int64))
            S.add_vecs(d, [S.to_vec(d, f)])
        return S

def par(m, h):
    """Partitions with at most h parts, size <= m, size = m (mod 2)."""
    out = []
    def rec(rem, mx, cur):
        if (m - sum(cur)) % 2 == 0: out.append(tuple(cur))
        if len(cur) == h: return
        for x in range(min(rem, mx), 0, -1):
            rec(rem - x, x, cur + [x])
    rec(m, m, [])
    return out

def leq(a, b):
    """Weak dominance a <= b."""
    sa = sb = 0
    for t in range(max(len(a), len(b))):
        sa += a[t] if t < len(a) else 0
        sb += b[t] if t < len(b) else 0
        if sa > sb: return False
    return True

def downsets(P):
    """All down-sets of the list of partitions P under weak dominance."""
    P = list(P); out = set()
    for mask in range(1 << len(P)):
        S = [P[i] for i in range(len(P)) if mask >> i & 1]
        if all(q in S for s in S for q in P if leq(q, s)):
            out.add(frozenset(S))
    return sorted(out, key=lambda s: (len(s), sorted(s)))

def interlaced(L0, L1):
    for (A, B) in ((L0, L1), (L1, L0)):
        for nu in A:
            for j in range(len(nu)):
                lo = list(nu); lo[j] -= 1
                if sh.norm(lo) not in B: return False
    return True
