"""Graded closure of a homogeneous ideal generated in one degree, in a box ring
F_p[v_1..v_n]/(v_i^box), using float64 BLAS with exact integer arithmetic (values < 2^53).
graded_dims(gens, nvars, box, p) -> (dims per degree as dict, total).
gens: list of dicts {exponent tuple: int coefficient}, all of the same total degree.
"""
import numpy as np, itertools, time

def monomials(nvars, box, d):
    """all exponent tuples of total degree d with entries in [0, box)."""
    out = []
    def rec(i, rem, cur):
        if i == nvars - 1:
            if rem < box: out.append(tuple(cur + [rem]))
            return
        for e in range(min(box - 1, rem) + 1):
            rec(i + 1, rem - e, cur + [e])
    if 0 <= d <= nvars * (box - 1): rec(0, d, [])
    return out

def rref_rows(C, p):
    """Row-reduce C (float64, entries in [0,p)) in place; return (rref rows, pivot cols)."""
    C = np.mod(C, p)
    nrows, ncols = C.shape
    pivots = []; r = 0
    for c in range(ncols):
        if r >= nrows: break
        col = C[r:, c]
        nz = np.flatnonzero(col)
        if nz.size == 0: continue
        i = r + int(nz[0])
        if i != r: C[[r, i]] = C[[i, r]]
        inv = pow(int(C[r, c]), p - 2, p)
        C[r] = np.mod(C[r] * inv, p)
        others = np.flatnonzero(C[:, c]); others = others[others != r]
        if others.size:
            C[others] = np.mod(C[others] - np.outer(C[others, c], C[r]), p)
        pivots.append(c); r += 1
    return C[:r], pivots

class RREF:
    def __init__(self, ncols, p):
        self.p = p; self.ncols = ncols
        self.B = np.zeros((0, ncols)); self.piv = []
    def insert_batch(self, C):
        p = self.p
        C = np.mod(C, p)
        if self.B.shape[0]:
            C = np.mod(C - C[:, self.piv] @ self.B, p)
        C = C[np.any(C, axis=1)]
        if C.shape[0] == 0: return 0
        R, pivC = rref_rows(C, p)
        if R.shape[0] == 0: return 0
        if self.B.shape[0]:
            self.B = np.mod(self.B - self.B[:, pivC] @ R, p)
        self.B = np.vstack([self.B, R]); self.piv += pivC
        return R.shape[0]
    def dim(self): return self.B.shape[0]

def graded_dims(gens, nvars, box, p, verbose=False):
    d0 = sum(next(iter(gens[0])))
    for g in gens:
        for e in g: assert sum(e) == d0 and max(e) < box
    dims = {}
    mons = monomials(nvars, box, d0); idx = {e: i for i, e in enumerate(mons)}
    C = np.zeros((len(gens), len(mons)))
    for gi, g in enumerate(gens):
        for e, c in g.items(): C[gi, idx[e]] = c % p
    B = RREF(len(mons), p); B.insert_batch(C)
    dims[d0] = B.dim()
    dmax = nvars * (box - 1)
    d = d0
    while d < dmax and B.dim() > 0:
        mons2 = monomials(nvars, box, d + 1); idx2 = {e: i for i, e in enumerate(mons2)}
        B2 = RREF(len(mons2), p)
        for i in range(nvars):
            src, dst = [], []
            for j, e in enumerate(mons):
                if e[i] < box - 1:
                    e2 = list(e); e2[i] += 1
                    src.append(j); dst.append(idx2[tuple(e2)])
            Cc = np.zeros((B.dim(), len(mons2)))
            Cc[:, dst] = B.B[:, src]
            B2.insert_batch(Cc)
        d += 1; mons, idx, B = mons2, idx2, B2
        dims[d] = B.dim()
        if verbose: print(f"    degree {d}: {len(mons)} monomials, dim {B.dim()}", flush=True)
    return dims, sum(dims.values())

# ---------- polynomial helpers (dict representation) ----------
def pmul(a, b, box=None):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            if box is not None and max(e) >= box: continue
            out[e] = out.get(e, 0) + ca * cb
    return {e: c for e, c in out.items() if c}

def binom_power(i, j, nvars, expo, sign_j=-1):
    """(v_i + sign_j*v_j)^expo as a dict."""
    from math import comb
    out = {}
    for s in range(expo + 1):
        e = [0] * nvars; e[i] = s; e[j] = expo - s
        out[tuple(e)] = comb(expo, s) * (sign_j ** (expo - s))
    return out
