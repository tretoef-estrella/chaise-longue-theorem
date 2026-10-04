# fria_engine.py — auditor's own engine for the cold audit of «Grepy is in the Sky» (Grepy Chats, 2 Oct 2026).
# Own code; nothing imported from the pilot. Box ring F_p[y_0..y_{m-1}]/(y_i^r), r odd; graded linear algebra.
# Objects built exactly as in PROOF_ODD_BOX.md: shapes Sh_m, interlaced pairs, patterns (Definition 4.1), V_Lambda, Z_Lambda, slices.
import itertools, sys
import numpy as np

# ---------- partitions and shapes ----------
def partitions(n, maxparts, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0: yield (); return
    if maxparts == 0: return
    for a in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - a, maxparts - 1, a): yield (a,) + rest

def Pset(n, h):
    return [lam for s in range(n % 2, n + 1, 2) for lam in partitions(s, h)] if n >= 0 else []

def Sh(m, h):
    return [(lam, 0) for lam in Pset(m, h)] + [(lam, 1) for lam in Pset(m - 1, h)]

def wdom(a, b):                      # weak dominance a ≼ b
    sa = sb = 0
    for t in range(max(len(a), len(b))):
        sa += a[t] if t < len(a) else 0; sb += b[t] if t < len(b) else 0
        if sa > sb: return False
    return True

def minus(lam, j):                   # remove a box from row j (0-based), re-sorted
    l = list(lam); l[j] -= 1
    return tuple(sorted([x for x in l if x > 0], reverse=True))
def plus(lam, j):
    l = list(lam); l[j] += 1
    return tuple(sorted(l, reverse=True))

def is_interlaced(L, m, h):
    L = set(L); S = Sh(m, h)
    for (lam, e) in L:
        for (mu, e2) in S:
            if e2 == e and wdom(mu, lam) and (mu, e2) not in L: return False      # (D1)
        for j in range(len(lam)):
            if (minus(lam, j), 1 - e) not in L: return False                       # (D2)
    return True

def interlaced_pairs(m, h):
    S = Sh(m, h); out = []
    for bits in range(1, 1 << len(S)):
        L = [S[i] for i in range(len(S)) if bits >> i & 1]
        if is_interlaced(L, m, h): out.append(frozenset(L))
    return out

def downset_pairs_not_interlaced(m, h):   # pairs of down-sets (D1) that fail (D2): for the negative control
    S = Sh(m, h); out = []
    for bits in range(1, 1 << len(S)):
        L = set(S[i] for i in range(len(S)) if bits >> i & 1)
        d1 = all((mu, e2) in L for (lam, e) in L for (mu, e2) in S if e2 == e and wdom(mu, lam))
        if d1 and not is_interlaced(L, m, h): out.append(frozenset(L))
    return out

# ---------- points ----------
def shape_of(M, h):
    cnt = {}
    for v in M: cnt[v] = cnt.get(v, 0) + 1
    lam = sorted([abs(cnt.get(u, 0) - cnt.get(-u, 0)) for u in range(1, h + 1) if cnt.get(u, 0) != cnt.get(-u, 0)], reverse=True)
    return (tuple(lam), cnt.get(0, 0) % 2)

def Zsize(L, m, h):
    return sum(1 for M in itertools.product(range(-h, h + 1), repeat=m) if shape_of(M, h) in L)

def F_formula(L, mu, e, h, r):       # (2.1) of the proof
    Le = {lam for (lam, x) in L if x == e}; Lo = {lam for (lam, x) in L if x == 1 - e}
    l = len(mu)
    f = sum(1 for j in range(l) if minus(mu, j) in Le) + sum(1 for j in range(l) if plus(mu, j) in Le)
    if l < h and (mu + (1,)) in Le: f += r - 1 - 2 * l
    return f + (1 if mu in Lo else 0)

def layers_formula(L, m, h, r):      # Lambda_i, i = 0..r-1
    S1 = Sh(m - 1, h)
    return [frozenset(s for s in S1 if F_formula(L, s[0], s[1], h, r) > i) for i in range(r)]

def layers_brute(L, m, h, r):        # for each tail, number of completions; returns dict shape -> set of counts, and sizes |Z_{>i}|
    by = {}; sizes = [0] * r
    for Mt in itertools.product(range(-h, h + 1), repeat=m - 1):
        c = sum(1 for y in range(-h, h + 1) if shape_of((y,) + Mt, h) in L)
        by.setdefault(shape_of(Mt, h), set()).add(c)
        for i in range(c): sizes[i] += 1
    return by, sizes

# ---------- the box ring ----------
class Box:
    def __init__(s, m, r, p):
        s.m, s.r, s.p, s.N = m, r, p, r ** m
        ex = np.array(list(itertools.product(range(r), repeat=m)), dtype=np.int64).reshape(-1, m) if m else np.zeros((1, 0), dtype=np.int64)
        s.ex = ex; s.deg = ex.sum(axis=1); s.maxdeg = m * (r - 1)
        s.cols = [np.flatnonzero(s.deg == d) for d in range(s.maxdeg + 1)]
    def zero(s): return np.zeros((s.r,) * s.m, dtype=np.int64)
    def one(s):
        A = s.zero(); A[(0,) * s.m] = 1; return A
    def var(s, i, e=1):
        A = s.zero(); x = [0] * s.m; x[i] = e
        if e < s.r: A[tuple(x)] = 1
        return A
    def mul(s, A, B):
        C = s.zero(); r = s.r
        for idx in zip(*np.nonzero(B)):
            c = int(B[idx]); src = tuple(slice(0, r - d) for d in idx); dst = tuple(slice(d, r) for d in idx)
            C[dst] += c * A[src]
        return C % s.p
    def D(s, a, b):                   # sum_{u} (-1)^u y_a^u y_b^{r-1-u}
        A = s.zero(); r = s.r
        for u in range(r):
            x = [0] * s.m; x[a] += u; x[b] += r - 1 - u; A[tuple(x)] += (-1) ** u
        return A % s.p
    def Bk(s, a, b):                  # sum_{u} (-1)^u y_a^u y_b^{r-2-u}
        A = s.zero(); r = s.r
        for u in range(r - 1):
            x = [0] * s.m; x[a] += u; x[b] += r - 2 - u; A[tuple(x)] += (-1) ** u
        return A % s.p
    def prod(s, L):
        A = s.one()
        for X in L: A = s.mul(A, X)
        return A
    def vdm(s, Sx):                   # prod_{c<c'} (y_{b_c'} - y_{b_c})
        A = s.one(); Sx = sorted(Sx)
        for i in range(len(Sx)):
            for j in range(i + 1, len(Sx)): A = s.mul(A, (s.var(Sx[j]) - s.var(Sx[i])) % s.p)
        return A
    def pf(s, idx, entry):            # Pfaffian of the alternating matrix entry(i,j), i<j in idx (expansion along the first index)
        if len(idx) == 0: return s.one()
        if len(idx) % 2: return s.zero()
        a = idx[0]; tot = s.zero()
        for k in range(1, len(idx)):
            b = idx[k]; E = entry(a, b)
            if E is None or not E.any(): continue
            sub = s.pf(idx[1:k] + idx[k + 1:], entry)
            if sub.any(): tot = (tot + (-1) ** (k - 1) * s.mul(E, sub)) % s.p
        return tot
    def pfE(s, M, E):                 # bordered Pfaffian Pf_E(M): variables M (sorted), borders y^e, e in E (sorted)
        M = sorted(M); E = sorted(E)
        idx = [('v', i) for i in M] + [('b', e) for e in E]
        def entry(x, y):
            if x[0] == 'v' and y[0] == 'v': return s.Bk(x[1], y[1])
            if x[0] == 'v' and y[0] == 'b': return s.var(x[1], y[1])
            return None
        return s.pf(idx, entry)
    # ---- graded linear algebra ----
    def echelon(s, M):
        p = s.p; r = 0; piv = []
        M = M % p
        for c in range(M.shape[1]):
            if r == M.shape[0]: break
            nz = np.flatnonzero(M[r:, c])
            if len(nz) == 0: continue
            i = nz[0] + r
            if i != r: M[[r, i]] = M[[i, r]]
            M[r] = (M[r] * pow(int(M[r, c]), -1, p)) % p
            o = np.flatnonzero(M[:, c]); o = o[o != r]
            if len(o): M[o] = (M[o] - M[o, c][:, None] * M[r][None, :]) % p
            piv.append(c); r += 1
        return M[:r], piv
    def hdeg(s, g):                   # degree of a homogeneous element (None if zero); asserts homogeneity
        nz = np.flatnonzero(g.reshape(-1))
        if len(nz) == 0: return None
        d = set(s.deg[nz].tolist()); assert len(d) == 1, "not homogeneous"
        return d.pop()
    def ideal(s, gens):               # graded basis: dict d -> (E over cols[d], piv)
        rows = {}; r = s.r
        for g in gens:
            dg = s.hdeg(g)
            if dg is None: continue
            for k in range(s.N):
                a = s.ex[k]; d = dg + int(s.deg[k])
                if d > s.maxdeg: continue
                src = tuple(slice(0, r - int(x)) for x in a); dst = tuple(slice(int(x), r) for x in a)
                C = s.zero(); C[dst] = g[src]
                v = C.reshape(-1)[s.cols[d]]
                if v.any():
                    rows.setdefault(d, []).append(v)
                    if len(rows[d]) >= 3000:          # chunked: reduce now, keep only the echelon basis (memory guard)
                        E, piv = s.echelon(np.array(rows[d], dtype=np.int64)); rows[d] = [x for x in E]
        out = {}
        for d, R in rows.items():
            E, piv = s.echelon(np.array(R, dtype=np.int64))
            if len(piv): out[d] = (E, piv)
        return out
    def add(s, bases):                # sum of graded subspaces
        out = {}
        ds = set(d for b in bases for d in b)
        for d in ds:
            E, piv = s.echelon(np.concatenate([b[d][0] for b in bases if d in b], axis=0))
            if len(piv): out[d] = (E, piv)
        return out
    @staticmethod
    def dim(b): return sum(len(v[1]) for v in b.values())
    def member(s, b, g):
        d = s.hdeg(g)
        if d is None: return True
        if d not in b: return False
        E, piv = b[d]; v = g.reshape(-1)[s.cols[d]] % s.p
        v = (v - v[piv] @ E) % s.p
        return not v.any()
    def slices(s, b):                 # W_j (j = 0..r-1) peeling variable 0, as graded bases in the box S2 of the other m-1 variables
        r = s.r; S2 = Box(s.m - 1, r, s.p); W = [dict() for _ in range(r)]
        for d, (E, piv) in b.items():
            cols = s.cols[d]; e0 = s.ex[cols, 0]
            order = np.argsort(-e0, kind='stable')                   # highest y_0-exponent first
            Eo, pv = s.echelon(E[:, order].copy())
            e0o = e0[order]; colso = cols[order]
            for row, pc in zip(Eo, pv):
                j = int(e0o[pc]); sel = np.flatnonzero(e0o == j)
                # the part of the row with y_0-exponent j, as a polynomial in the other variables
                tail_idx = colso[sel] % (r ** (s.m - 1))            # index of the other exponents (variable 0 is the most significant digit)
                g = np.zeros(S2.N, dtype=np.int64); g[tail_idx] = row[sel]
                W[j].setdefault(d - j, []).append(g[S2.cols[d - j]])
        out = []
        for j in range(r):
            bj = {}
            for d, R in W[j].items():
                E, piv = S2.echelon(np.array(R, dtype=np.int64))
                if len(piv): bj[d] = (E, piv)
            out.append(bj)
        return S2, out

# ---------- patterns (Definition 4.1) ----------
def kpairs(S, k):
    S = list(S)
    if k == 0: yield (); return
    if len(S) < 2 * k: return
    a = S[0]; rest = S[1:]
    for i, b in enumerate(rest):
        for M in kpairs(rest[:i] + rest[i + 1:], k - 1): yield ((a, b),) + M
    yield from kpairs(rest, k)

def blocks(S, sizes):                 # ordered partitions of S into blocks of the given sizes
    S = list(S)
    if not sizes:
        if not S: yield ()
        return
    for B in itertools.combinations(S, sizes[0]):
        rest = [x for x in S if x not in B]
        for more in blocks(rest, sizes[1:]): yield (B,) + more

def columns(lam):
    return [sum(1 for x in lam if x >= c) for c in range(1, (lam[0] if lam else 0) + 1)]

def E_of(l, r): return [r - 1] if l == 0 else list(range(0, l - 1))

def pattern_products(R, shape, idx, tmax=None):
    lam, e = shape; r = R.r; n = len(idx); l = len(lam); cols = columns(lam); out = []
    if e == 0:
        if (n - sum(lam)) % 2 or n < sum(lam): return out
        for P in kpairs(idx, (n - sum(lam)) // 2):
            used = {x for pr in P for x in pr}; rest = [x for x in idx if x not in used]
            DP = R.prod([R.D(a, b) for a, b in P])
            for Bs in blocks(rest, cols):
                out.append(R.prod([DP] + [R.vdm(B) for B in Bs]))
    else:
        base = n - 1 - sum(lam)
        if base % 2 or base < 0: return out
        for t in range(0, base // 2 + 1):
            if tmax is not None and t > tmax: break
            for Mk in itertools.combinations(idx, l + 1 + 2 * t):
                rest0 = [x for x in idx if x not in Mk]
                PF = R.pfE(Mk, E_of(l, r))
                if not PF.any(): continue
                for P in kpairs(rest0, base // 2 - t):
                    used = {x for pr in P for x in pr}; rest = [x for x in rest0 if x not in used]
                    DP = R.prod([R.D(a, b) for a, b in P])
                    for Bs in blocks(rest, cols[1:]):
                        out.append(R.prod([PF, DP] + [R.vdm(B) for B in Bs]))
    return out
