# regla276 — gate for Theorem 5.11 of PAPER_OFICIAL_v4 (equality dim V_Lambda = |Z_Lambda| when char F does not divide q-1).
# Grepy el Auditor, 2026-09-25. ESTIMATE (written before running): largest ring C_4 at q=7 has 6^4 = 1296 monomials;
# ideal = span(gens x monomials) as a dense int64 matrix of at most a few thousand rows x 1296 columns: < 50 MB, < 60 s.
# [v2, after the watchdog stopped v1 at 1.26 GB: the dense matrix was built all at once. Now an incremental echelon basis
#  of at most 1296 rows (13 MB) and closure under multiplication by the variables. Estimate: < 100 MB, < 10 min.]
# Gates:
#  G1 evaluation: over F_q with q = p (p = 5, 7) and q = 9 (F_9 = F_3[i]/(i^2+1)), D(a,b) != 0 on T x T iff b = -a.
#  G2 support: for every M in T^m and every lambda in Par_m, "some tight pattern of lambda is non-zero at M"
#      (brute force over pairs and column fillings) iff lambda(M) <= lambda (weak dominance).
#  G3 algebra: dim_F V_Lambda = |Z_Lambda| for EVERY down-set, over F_p with p not dividing q-1:
#      (q,p) = (5,5),(5,7),(5,3),(7,7),(7,5) at m = 2,3,4; control cell (7,3) where 3 | 6 (outside the theorem).
import itertools, sys
import numpy as np

def parts_all(m, h):
    out = []
    def rec(rem, maxp, cur):
        out.append(tuple(cur))
        for x in range(min(rem, maxp), 0, -1):
            if len(cur) < h: rec(rem - x, x, cur + [x])
    rec(m, m, [])
    return sorted(set(l for l in out if (m - sum(l)) % 2 == 0), key=lambda l: (sum(l), l))

def S(l, t): return sum(sorted(l, reverse=True)[:t])
def leq(a, b):
    T = max(len(a), len(b), 1)
    return all(S(a, t) <= S(b, t) for t in range(1, T + 1))

def lam_of(M, q):  # values 0..q-2, negation v <-> v^1
    cnt = {}
    for v in M: cnt[v] = cnt.get(v, 0) + 1
    res = []
    for c in range((q - 1) // 2):
        a, b = cnt.get(2 * c, 0), cnt.get(2 * c + 1, 0)
        if a != b: res.append(abs(a - b))
    return tuple(sorted(res, reverse=True))

def conj(l):
    return [sum(1 for x in l if x > c) for c in range(l[0])] if l else []

def tight_patterns(idx, l):
    """yield (pairs, blocks) : pairs a list of (a<b), blocks a list of sorted tuples with sizes = columns of l"""
    m = len(idx); pnum = (m - sum(l)) // 2; cols = conj(l)
    for pairset in itertools.combinations(idx, 2 * pnum):
        rest = [i for i in idx if i not in pairset]
        def matchings(pts):
            if not pts: yield []; return
            a = pts[0]
            for j in range(1, len(pts)):
                for mm in matchings(pts[1:j] + pts[j + 1:]): yield [(a, pts[j])] + mm
        def fills(pts, cs):
            if not cs: yield []; return
            for blk in itertools.combinations(pts, cs[0]):
                rem = [x for x in pts if x not in blk]
                for f in fills(rem, cs[1:]): yield [blk] + f
        for P in matchings(list(pairset)):
            for B in fills(rest, cols): yield P, B

def G2(q, m):
    """forward: a non-zero pattern of lambda at M forces lambda(M) <= lambda (needed for the upper bound);
    self: some pattern of lambda(M) is non-zero at M (gives support = Z_Lambda for down-sets).
    The converse for EVERY lambda >= lambda(M) is false and not claimed (e.g. M=(0,0,1), lambda=(1,1,1))."""
    h = (q - 1) // 2; Pm = parts_all(m, h); fwd = 0; selfbad = 0; tests = 0
    pats = {l: list(tight_patterns(list(range(m)), l)) for l in Pm}
    def nz(M, l): return any(all(M[b] == (M[a] ^ 1) for a, b in P) and all(len(set(M[i] for i in blk)) == len(blk) for blk in B) for P, B in pats[l])
    for M in itertools.product(range(q - 1), repeat=m):
        lm = lam_of(M, q)
        if not nz(M, lm): selfbad += 1
        for l in Pm:
            tests += 1
            if nz(M, l) and not leq(lm, l): fwd += 1
    return tests, fwd, selfbad

# ---- G1 ----
def G1():
    out = []
    for p in (5, 7):
        q = p; T = list(range(1, q)); bad = 0
        for a in T:
            for b in T:
                D = sum(((-1) ** u) * pow(a, u, p) * pow(b, q - 2 - u, p) for u in range(q - 1)) % p
                if (D != 0) != ((a + b) % p == 0): bad += 1
        out.append((q, bad))
    # F_9 = F_3[i]/(i^2+1), elements (x,y) = x + y i
    def mul(u, v): return ((u[0] * v[0] - u[1] * v[1]) % 3, (u[0] * v[1] + u[1] * v[0]) % 3)
    def pw(u, e):
        r = (1, 0)
        for _ in range(e): r = mul(r, u)
        return r
    T = [(x, y) for x in range(3) for y in range(3) if (x, y) != (0, 0)]; bad = 0
    for a in T:
        for b in T:
            s = (0, 0)
            for u in range(8):
                t = mul(pw(a, u), pw(b, 7 - u)); sg = 1 if u % 2 == 0 else 2
                s = ((s[0] + sg * t[0]) % 3, (s[1] + sg * t[1]) % 3)
            neg = ((a[0] + b[0]) % 3, (a[1] + b[1]) % 3) == (0, 0)
            if (s != (0, 0)) != neg: bad += 1
    out.append((9, bad))
    return out

# ---- G3 ----
def rank_mod(A, p):
    A = A.copy() % p; r = 0; rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c]: piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p); A[r] = (A[r] * inv) % p
        nz = np.nonzero(A[:, c])[0]
        for i in nz:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
        if r == rows: break
    return r

def poly_mul(f, g, e):  # dicts exponent-tuple -> coeff, truncate exponents > e
    out = {}
    for a, x in f.items():
        for b, y in g.items():
            c = tuple(i + j for i, j in zip(a, b))
            if max(c) <= e: out[c] = out.get(c, 0) + x * y
    return out

def G3(q, p, m):
    h = (q - 1) // 2; e = q - 2; Pm = parts_all(m, h)
    mons = list(itertools.product(range(q - 1), repeat=m)); mi = {x: i for i, x in enumerate(mons)}
    def var(i, d): t = [0] * m; t[i] = d; return tuple(t)
    def Dp(a, b): return {tuple(sum(z) for z in zip(var(a, u), var(b, q - 2 - u))): (-1) ** u for u in range(q - 1)}
    def Delta(B):
        f = {tuple([0] * m): 1}
        for x, y in itertools.combinations(B, 2):  # (y_y - y_x)
            f = poly_mul(f, {var(y, 1): 1, var(x, 1): -1}, e)
        return f
    gens = {}
    for l in Pm:
        G = []
        for P, B in tight_patterns(list(range(m)), l):
            f = {tuple([0] * m): 1}
            for a, b in P: f = poly_mul(f, Dp(a, b), e)
            for blk in B: f = poly_mul(f, Delta(blk), e)
            f = {k: v % p for k, v in f.items() if v % p}
            if f: G.append(f)
        gens[l] = G
    # counts |Z_lambda|
    cnt = {l: 0 for l in Pm}
    for M in itertools.product(range(q - 1), repeat=m): cnt[lam_of(M, q)] += 1
    res = []; allok = True
    idx = list(range(len(Pm)))
    for bits in range(1 << len(Pm)):
        L = [Pm[i] for i in idx if bits >> i & 1]
        if any(leq(x, y) and x not in L for y in L for x in Pm): continue  # not a down-set
        # incremental closure: span of generators, then multiply the basis by the variables until stable
        basis = {}  # pivot column -> reduced row (int64, entries mod p)
        def add(v):
            v = v % p
            for c in sorted(basis):
                if v[c]: v = (v - v[c] * basis[c]) % p
            nzc = np.nonzero(v)[0]
            if len(nzc) == 0: return False
            c = int(nzc[0]); v = (v * pow(int(v[c]), p - 2, p)) % p
            for c2 in list(basis):
                if basis[c2][c]: basis[c2] = (basis[c2] - basis[c2][c] * v) % p
            basis[c] = v; return True
        def vec(f):
            v = np.zeros(len(mons), dtype=np.int64)
            for k2, c in f.items(): v[mi[k2]] = (v[mi[k2]] + c) % p
            return v
        for l in L:
            for g in gens[l]: add(vec(g))
        grew = True
        while grew:
            grew = False
            for r in list(basis.values()):
                for i in range(m):
                    w = np.zeros(len(mons), dtype=np.int64)
                    for j in np.nonzero(r)[0]:
                        t = list(mons[j]); t[i] += 1
                        if t[i] <= e: w[mi[tuple(t)]] = (w[mi[tuple(t)]] + r[j]) % p
                    if w.any() and add(w): grew = True
        dimV = len(basis)
        Z = sum(cnt[l] for l in L)
        res.append((len(L), dimV, Z)); allok &= (dimV == Z)
    return res, allok

if __name__ == '__main__':
    print('G1 evaluation (q, failures):', G1(), flush=True)
    for q, m in ((5, 3), (5, 4), (7, 3), (9, 3), (9, 4)):
        print('G2 support q=%d m=%d: tests=%d forward-failures=%d self-pattern-failures=%d' % ((q, m) + G2(q, m)), flush=True)
    for q, p, m in ((5, 5, 3), (5, 5, 4), (5, 7, 4), (5, 3, 4), (7, 7, 3), (7, 5, 3), (7, 7, 4), (7, 3, 3), (7, 3, 4)):
        res, ok = G3(q, p, m)
        tag = 'CONTROL (p | q-1, outside the theorem)' if (q - 1) % p == 0 else 'in the theorem'
        print('G3 q=%d p=%d m=%d [%s]: down-sets=%d all equal=%s  %s' % (q, p, m, tag, len(res), ok, res), flush=True)
    print('FIN-OK')
