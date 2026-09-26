"""Tiny exact linear algebra over F_3 with numpy (int8), incremental echelon form.
Rows are reduced against a basis kept in *reduced* row echelon form with pivot = first nonzero column.
"""
import numpy as np

class Echelon:
    def __init__(self, ncols):
        self.n = ncols
        self.rows = []          # list of np.int8 arrays (reduced)
        self.pivots = []        # pivot column of each row
        self.pivmap = {}        # col -> index in rows
    def rank(self): return len(self.rows)
    def reduce(self, v):
        """reduce v (int8 array mod 3) fully against basis; returns reduced vector"""
        v = v % 3
        nz = np.flatnonzero(v)
        # iterative: reduce leading pivot cols in order
        while True:
            hit = [c for c in nz if c in self.pivmap]
            if not hit: return v
            for c in hit:
                idx = self.pivmap[c]
                coef = v[c]
                if coef:
                    v = (v - coef * self.rows[idx]) % 3
            nz = np.flatnonzero(v)
            # after reducing hit columns, new nonzeros can only appear at columns > pivot; loop handles them
            if not any(c in self.pivmap for c in nz): return v
    def add(self, v):
        """add vector to the span; return True if rank grew"""
        v = self.reduce(v)
        nz = np.flatnonzero(v)
        if len(nz) == 0: return False
        p = nz[0]
        if v[p] == 2: v = (2 * v) % 3   # normalise pivot to 1
        # reduce existing rows at column p
        for i, r in enumerate(self.rows):
            if r[p]:
                self.rows[i] = (r - r[p] * v) % 3
        self.rows.append(v.astype(np.int8)); self.pivots.append(int(p)); self.pivmap[int(p)] = len(self.rows) - 1
        return True
    def add_many(self, M):
        """M: 2D int8 array (rows). Batch: reduce all rows against current basis, then gaussian within batch."""
        M = (np.asarray(M, dtype=np.int64) % 3).astype(np.int8)
        if M.shape[0] == 0: return
        # reduce against existing basis (dense, column by column in pivot order)
        if self.rows:
            B = np.stack(self.rows).astype(np.int64)
            piv = np.array(self.pivots)
            X = M.astype(np.int64)
            # since basis is reduced, coefficient of each row = X[:, pivot]
            coefs = X[:, piv] % 3
            X = (X - coefs @ B) % 3
            M = X.astype(np.int8)
        # gaussian elimination inside the batch
        X = M.astype(np.int64)
        newrows = []
        for _ in range(X.shape[0]):
            nzr = np.flatnonzero(X.any(axis=1))
            if len(nzr) == 0: break
            # pick row with smallest leading column
            lead = np.array([np.flatnonzero(X[r])[0] for r in nzr])
            k = nzr[np.argmin(lead)]
            p = lead[np.argmin(lead)]
            v = X[k] % 3
            if v[p] == 2: v = (2 * v) % 3
            col = X[:, p] % 3
            X = (X - np.outer(col, v)) % 3
            X[k] = 0
            newrows.append((int(p), v.astype(np.int8)))
        # reduce new rows among themselves (they are already echelon w.r.t. each other's pivots, since we eliminated column p in all others)
        for p, v in newrows:
            # reduce existing basis rows at column p
            for i, r in enumerate(self.rows):
                if r[p]:
                    self.rows[i] = (r - int(r[p]) * v) % 3
            self.rows.append(v); self.pivots.append(p); self.pivmap[p] = len(self.rows) - 1
    def contains(self, v):
        return not np.flatnonzero(self.reduce(np.asarray(v, dtype=np.int8) % 3)).size
