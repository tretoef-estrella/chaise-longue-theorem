"""
gf_linalg.py — small finite-field linear algebra for the cold audit (referee's own code), v3 (memory-bounded, block storage).

* GF(p, d): the field F_{p^d}, elements encoded as integers 0..p^d-1 (base-p digits = coefficients of a
  polynomial of degree < d in a root s of a monic irreducible f).  Tables add, sub, mul, inv.  For d = 1 all
  arithmetic is done directly mod p on integer arrays (no tables, no big index temporaries).
* gf_matmul(gf, A, B): product of int-encoded matrices, done as d^2 products of F_p matrices with float32 BLAS
  (exact while k*(p-1)^2 < 2^24).
* Span(gf, ncols): an incrementally built reduced row echelon basis of a subspace of F^{ncols}.  add(N) reduces a
  batch N against the basis (one chunked matmul per batch), echelonises the remainder hierarchically (matmul on
  sub-batches of 32, naive elimination inside a sub-batch), and keeps the basis reduced.  All float32 temporaries
  are chunked to <= ~32 MB.  dim() is the rank.

Everything is written from scratch; nothing is taken from the paper.
"""
import numpy as np
import itertools

CHUNK_BYTES = 32_000_000  # bound on float32 temporaries

class GF:
    def __init__(self, p, d, poly=None):
        self.p, self.d = int(p), int(d)
        self.n = self.p ** self.d
        self.poly = None if self.d == 1 else (poly if poly is not None else self._find_irreducible())
        self._build()

    def _polmulmod(self, a, b, f):
        p = self.p; d = self.d
        res = [0] * (2 * d - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    res[i + j] = (res[i + j] + ai * bj) % p
        for k in range(2 * d - 2, d - 1, -1):
            c = res[k]
            if c:
                for j in range(d + 1):
                    res[k - d + j] = (res[k - d + j] - c * f[j]) % p
        return res[:d]

    def _is_irreducible(self, f):
        p, d = self.p, self.d
        def polydivmod(num, den):
            num = num[:]; dd = len(den) - 1
            while len(num) - 1 >= dd and any(num):
                if num[-1] == 0:
                    num.pop(); continue
                c = num[-1]; shift = len(num) - 1 - dd
                for j in range(dd + 1):
                    num[shift + j] = (num[shift + j] - c * den[j]) % p
                num.pop()
            return num
        for e in range(1, d // 2 + 1):
            for coeffs in itertools.product(range(p), repeat=e):
                g = list(coeffs) + [1]
                if not any(polydivmod(list(f), g)):
                    return False
        return True

    def _find_irreducible(self):
        p, d = self.p, self.d
        for coeffs in itertools.product(range(p), repeat=d):
            f = list(coeffs) + [1]
            if f[0] == 0:
                continue
            if self._is_irreducible(f):
                return f
        raise RuntimeError("no irreducible found")

    def _build(self):
        p, d, n = self.p, self.d, self.n
        idx = np.arange(n)
        digits = np.stack([(idx // p ** j) % p for j in range(d)], axis=1)
        self.digits = digits
        self.pow_p = np.array([p ** j for j in range(d)], dtype=np.int64)
        self.dtype = np.uint8 if n <= 255 else (np.uint16 if n <= 65535 else np.int64)
        if d == 1 and n > 256:
            # large prime field: no tables (vsub/vscale/gf_matmul use direct arithmetic); only inverses
            self.add = self.sub = self.neg = self.mul = None
            self.red = np.ones((1, 1), dtype=np.int64)
            self.inv = np.array([0] + [pow(a, p - 2, p) for a in range(1, n)], dtype=self.dtype)
            return
        self.add = (((digits[:, None, :] + digits[None, :, :]) % p) @ self.pow_p).astype(self.dtype)
        self.sub = (((digits[:, None, :] - digits[None, :, :]) % p) @ self.pow_p).astype(self.dtype)
        self.neg = (((-digits) % p) @ self.pow_p).astype(self.dtype)
        if d == 1:
            self.mul = ((idx[:, None] * idx[None, :]) % p).astype(self.dtype)
            self.red = np.ones((1, 1), dtype=np.int64)
        else:
            red = np.zeros((2 * d - 1, d), dtype=np.int64)
            cur = [1] + [0] * (d - 1)
            for k in range(2 * d - 1):
                red[k] = cur
                cur = self._polmulmod(cur, [0, 1] + [0] * (d - 2), self.poly)
            self.red = red
            A = digits
            prod = np.zeros((n, n, 2 * d - 1), dtype=np.int64)
            for i in range(d):
                for j in range(d):
                    prod[:, :, i + j] += A[:, None, i] * A[None, :, j]
            prod %= p
            self.mul = (((prod @ red) % p) @ self.pow_p).astype(self.dtype)
        inv = np.zeros(n, dtype=np.int64)
        for a in range(1, n):
            b = np.nonzero(self.mul[a] == 1)[0]
            assert len(b) == 1
            inv[a] = b[0]
        self.inv = inv.astype(self.dtype)

    # scalar helpers
    def power(self, a, e):
        r = 1; b = int(a); e = int(e)
        while e:
            if e & 1:
                r = int(self.mul[r, b])
            b = int(self.mul[b, b]); e >>= 1
        return r

    def order(self, a):
        k = 1; x = int(a)
        while x != 1:
            x = int(self.mul[x, int(a)]); k += 1
            if k > self.n: raise RuntimeError
        return k

    def primitive_root_of_unity(self, r):
        assert (self.n - 1) % r == 0
        for g in range(2, self.n):
            x = self.power(g, (self.n - 1) // r)
            if x != 1 and self.order(x) == r:
                return x
        raise RuntimeError

    # vector ops (arrays of encoded elements)
    def vsub(self, X, Y):
        if self.d == 1:
            t = np.int16 if self.p < 128 else np.int64
            return ((X.astype(t) - Y.astype(t)) % self.p).astype(self.dtype)
        return self.sub[X, Y]

    def vscale(self, c, X):
        """c * X for a scalar c"""
        if self.d == 1:
            t = np.int16 if self.p < 128 else np.int64
            return ((int(c) * X.astype(t)) % self.p).astype(self.dtype)
        return self.mul[c, X]

    def to_components(self, A):
        if self.d == 1:
            return [np.asarray(A).astype(np.float32)]
        A = np.asarray(A).astype(np.int64)
        return [((A // self.pow_p[j]) % self.p).astype(np.float32) for j in range(self.d)]

    def from_components(self, comps):
        if self.d == 1:
            return comps[0].astype(self.dtype)
        out = np.zeros(comps[0].shape, dtype=np.int64)
        for j in range(self.d):
            out += comps[j].astype(np.int64) * self.pow_p[j]
        return out.astype(self.dtype)

def gf_matmul(gf, A, B):
    """A (r x k), B (k x c) int-encoded -> A@B int-encoded (exact, float32 BLAS)."""
    p, d = gf.p, gf.d
    k = A.shape[1]
    if d == 1 and k * (p - 1) ** 2 >= 2 ** 24:
        # large prime field: exact float64 BLAS (sums stay below 2^53)
        assert k * (p - 1) ** 2 < 2 ** 53, "inner dimension too large for exact float64"
        M = np.asarray(A).astype(np.float64) @ np.asarray(B).astype(np.float64)
        np.fmod(M, p, out=M)
        return M.astype(gf.dtype)
    assert k * (p - 1) ** 2 < 2 ** 24, "inner dimension too large for exact float32"
    Ac = gf.to_components(A); Bc = gf.to_components(B)
    if d == 1:
        M = Ac[0] @ Bc[0]
        np.fmod(M, p, out=M)
        return M.astype(gf.dtype)
    out = [np.zeros((A.shape[0], B.shape[1]), dtype=np.float32) for _ in range(d)]
    red = gf.red
    for i in range(d):
        for j in range(d):
            M = Ac[i] @ Bc[j]
            np.fmod(M, p, out=M)
            for l in range(d):
                c = int(red[i + j, l])
                if c:
                    out[l] += c * M
    comps = []
    for o in out:
        np.fmod(o, p, out=o)
        comps.append(o)
    return gf.from_components(comps)

class Span:
    """Reduced row echelon basis of a subspace of F^{ncols}, built incrementally (memory-bounded, v3).
    The basis is stored as a list of blocks (rows, pivot columns); the blocks are mutually reduced
    (every row has 0 at the pivot columns of every other block), so the union is an RREF basis."""
    def __init__(self, gf, ncols, batch=256, inner=32, max_blocks=48):
        self.gf = gf; self.ncols = ncols
        self.blocks = []  # list of [R (k_b x ncols), pcs (list of ints)]
        self.batch = batch; self.inner = inner; self.max_blocks = max_blocks

    def dim(self):
        return sum(R.shape[0] for R, _ in self.blocks)

    @property
    def pc(self):
        out = []
        for _, pcs in self.blocks:
            out += pcs
        return out

    @property
    def B(self):
        if not self.blocks:
            return np.zeros((0, self.ncols), dtype=self.gf.dtype)
        return np.vstack([R for R, _ in self.blocks])

    def _colchunk(self, k):
        return max(64, int(CHUNK_BYTES // max(1, 4 * k)))

    def _reduce_one(self, N, R, pcs):
        """N -= N[:, pcs] @ R (chunked over columns)"""
        if R.shape[0] == 0 or N.shape[0] == 0:
            return N
        gf = self.gf
        C = N[:, pcs]
        w = self._colchunk(max(N.shape[0], R.shape[0]))
        for c0 in range(0, self.ncols, w):
            c1 = min(self.ncols, c0 + w)
            prod = gf_matmul(gf, C, R[:, c0:c1])
            N[:, c0:c1] = gf.vsub(N[:, c0:c1], prod)
        return N

    def _reduce(self, N, blocks):
        N = N.copy()
        for R, pcs in blocks:
            N = self._reduce_one(N, R, pcs)
        return N

    def _naive_rref(self, N):
        gf = self.gf
        rows = []; pcs = []
        for v in N:
            v = v.copy()
            for (r, pcol) in zip(rows, pcs):
                c = v[pcol]
                if c:
                    v = gf.vsub(v, gf.vscale(c, r))
            nz = np.nonzero(v)[0]
            if len(nz) == 0:
                continue
            pcol = int(nz[0])
            v = gf.vscale(gf.inv[v[pcol]], v)
            for i in range(len(rows)):
                c = rows[i][pcol]
                if c:
                    rows[i] = gf.vsub(rows[i], gf.vscale(c, v))
            rows.append(v); pcs.append(pcol)
        if rows:
            return np.array(rows, dtype=gf.dtype), pcs
        return np.zeros((0, self.ncols), dtype=gf.dtype), []

    def _echelonise(self, N):
        """hierarchical RREF of a batch already reduced against the basis; returns one block (R, pcs)"""
        tmp = []  # small blocks
        for s in range(0, N.shape[0], self.inner):
            Ns = self._reduce(N[s:s + self.inner], tmp)
            Rs, ps = self._naive_rref(Ns)
            if Rs.shape[0] == 0:
                continue
            for blk in tmp:
                blk[0] = self._reduce_one(blk[0], Rs, ps)
            tmp.append([Rs, ps])
        if not tmp:
            return np.zeros((0, self.ncols), dtype=self.gf.dtype), []
        R = np.vstack([b[0] for b in tmp]); pcs = []
        for b in tmp:
            pcs += b[1]
        return R, pcs

    def _compact(self):
        if len(self.blocks) <= self.max_blocks:
            return
        # merge the smallest blocks (each < 4*batch rows) into one
        small = [b for b in self.blocks if b[0].shape[0] < 4 * self.batch]
        big = [b for b in self.blocks if b[0].shape[0] >= 4 * self.batch]
        if len(small) >= 2:
            R = np.vstack([b[0] for b in small]); pcs = []
            for b in small:
                pcs += b[1]
            self.blocks = big + [[R, pcs]]

    def add(self, N):
        """add the rows of N to the span; returns the new echelon rows actually added"""
        gf = self.gf
        N = np.asarray(N, dtype=gf.dtype)
        if N.ndim == 1:
            N = N[None, :]
        added = []
        for s in range(0, N.shape[0], self.batch):
            Nb = self._reduce(N[s:s + self.batch], self.blocks)
            R, pcs = self._echelonise(Nb)
            if R.shape[0] == 0:
                continue
            for blk in self.blocks:
                blk[0] = self._reduce_one(blk[0], R, pcs)
            self.blocks.append([R, pcs])
            self._compact()
            added.append(R)
        if added:
            return np.vstack(added)
        return np.zeros((0, self.ncols), dtype=gf.dtype)

def rank_mod_p(M, p, batch=256):
    gf = GF(p, 1)
    S = Span(gf, M.shape[1], batch=batch)
    S.add(np.asarray(M) % p)
    return S.dim()

if __name__ == "__main__":
    import time, resource
    rng = np.random.default_rng(1)
    for p in (3, 5, 7):
        A = rng.integers(0, p, size=(400, 70)); Bm = rng.integers(0, p, size=(70, 3000))
        M = (A @ Bm) % p
        r = rank_mod_p(M, p)
        assert r == 70, r
        # compare with a sympy-free check: rank over F_p of M plus one dependent row unchanged
        M2 = np.vstack([M, (M[0] + 2 * M[1]) % p])
        assert rank_mod_p(M2, p) == 70
        print("p", p, "rank", r, "ok")
    for (p, d) in ((3, 4), (5, 2), (3, 6), (7, 1)):
        t = time.time(); gf = GF(p, d); print("GF", p, d, "poly", gf.poly, "built in %.2fs" % (time.time() - t))
        n = gf.n
        a, b, c = rng.integers(1, n, size=3)
        assert gf.mul[a, gf.inv[a]] == 1
        assert gf.mul[a, gf.add[b, c]] == gf.add[gf.mul[a, b], gf.mul[a, c]]
        assert gf.mul[gf.mul[a, b], c] == gf.mul[a, gf.mul[b, c]]
        for r in [x for x in (3, 5, 7) if (n - 1) % x == 0]:
            z = gf.primitive_root_of_unity(r); assert gf.order(z) == r
        A = rng.integers(0, n, size=(5, 6)).astype(gf.dtype); Bm = rng.integers(0, n, size=(6, 4)).astype(gf.dtype)
        C = gf_matmul(gf, A, Bm)
        for i in range(5):
            for j in range(4):
                s = 0
                for k in range(6):
                    s = gf.add[s, gf.mul[A[i, k], Bm[k, j]]]
                assert s == C[i, j]
        X = rng.integers(0, n, size=(200, 37)).astype(gf.dtype); Y = rng.integers(0, n, size=(37, 500)).astype(gf.dtype)
        M = gf_matmul(gf, X, Y)
        S = Span(gf, 500, batch=64, inner=8); S.add(M)
        assert S.dim() == 37, S.dim()
        # basis must be in RREF: B[:, pc] = identity
        I = S.B[:, S.pc]
        assert np.array_equal(I, np.eye(37, dtype=I.dtype))
        print("  GF(%d^%d) ok, span rank" % (p, d), S.dim())
    print("peak RSS MB", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6)
    print("ALL SELF-TESTS PASSED")
