"""Shared engine: incremental reduced-row-echelon basis over F_p (numpy, int64).

RREFBasis(ncols, p, maxrows): rows are kept in reduced echelon form so that
reducing a vector is a single matrix-vector product.
"""
import numpy as np

class RREFBasis:
    def __init__(self, ncols, p, maxrows):
        self.p = p
        self.ncols = ncols
        self.B = np.zeros((maxrows, ncols), dtype=np.int64)
        self.piv = []            # pivot column of each row
        self.pivrow = -np.ones(ncols, dtype=np.int64)
        self.n = 0

    def reduce(self, v):
        """Return v reduced modulo the span (exact, since B is in RREF)."""
        v = np.asarray(v, dtype=np.int64) % self.p
        if self.n:
            c = v[self.piv]
            if c.any():
                v = (v - c @ self.B[:self.n]) % self.p
        return v

    def insert(self, v):
        """Reduce v and insert it if non-zero. Returns True if inserted."""
        v = self.reduce(v)
        nz = np.flatnonzero(v)
        if nz.size == 0:
            return False
        c = int(nz[0])
        inv = pow(int(v[c]), self.p - 2, self.p)
        v = (v * inv) % self.p
        if self.n:
            col = self.B[:self.n, c].copy()
            rows = np.flatnonzero(col)
            if rows.size:
                self.B[rows] = (self.B[rows] - np.outer(col[rows], v)) % self.p
        if self.n >= self.B.shape[0]:
            self.B = np.vstack([self.B, np.zeros((max(64, self.n // 2), self.ncols), dtype=np.int64)])
        self.B[self.n] = v
        self.piv.append(c)
        self.pivrow[c] = self.n
        self.n += 1
        return True

    def dim(self):
        return self.n
