# chkE10.py — brute force for Lean piece E10 (q_membership.md): Lemma 8.7 of paper v11 (the
# membership lemma), in the Pfaffian form that follows from E9 (S5), E8 (A1), (B5) and (S3).
# Grepy Mandalay, 2 Oct 2026. Exact integer arithmetic, no external library.
#
# Rings: Box(n, r) = Z[y_0..y_{n-1}]/(y_i^r) (r = None: the polynomial ring, no truncation);
#        Zeta(K)   = K[zeta], lists of elements of K.
import itertools, random, sys
random.seed(20261002)
NCHK = 0; NFAIL = 0; NCTL = 0; NCTLFIRE = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1; print("FAIL", name); sys.stdout.flush()
def control(name, fires):
    global NCTL, NCTLFIRE
    NCTL += 1
    if fires: NCTLFIRE += 1
    print("control", name, "FIRES" if fires else "SILENT"); sys.stdout.flush()

class Box:
    def __init__(self, n, r):
        self.n = n; self.r = r
        self.zero = {}
        self.one = {(0,)*n: 1}
    def const(self, c): return {(0,)*self.n: c} if c else {}
    def var(self, i, e=1):
        if self.r is not None and e >= self.r: return {}
        t = [0]*self.n; t[i] = e
        return {tuple(t): 1}
    def add(self, p, q):
        res = dict(p)
        for k, v in q.items():
            w = res.get(k, 0) + v
            if w: res[k] = w
            else: res.pop(k, None)
        return res
    def neg(self, p): return {k: -v for k, v in p.items()}
    def sub(self, p, q): return self.add(p, self.neg(q))
    def mul(self, p, q):
        res = {}
        r = self.r
        if len(p) > len(q): p, q = q, p
        for k1, v1 in p.items():
            for k2, v2 in q.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                if r is not None and max(k) >= r: continue
                w = res.get(k, 0) + v1*v2
                if w: res[k] = w
                else: res.pop(k, None)
        return res
    def scal(self, c, p): return {k: c*v for k, v in p.items()} if c else {}
    def eq(self, p, q): return p == q
    def iszero(self, p): return not p

class Zeta:
    def __init__(self, K):
        self.K = K; self.zero = []; self.one = [K.one]
    def norm(self, p):
        p = list(p)
        while p and self.K.iszero(p[-1]): p.pop()
        return p
    def const(self, a): return self.norm([a])
    def mono(self, a, d): return self.norm([self.K.zero]*d + [a])
    def add(self, p, q):
        m = max(len(p), len(q)); K = self.K
        return self.norm([K.add(p[i] if i < len(p) else K.zero, q[i] if i < len(q) else K.zero) for i in range(m)])
    def neg(self, p): return [self.K.neg(a) for a in p]
    def sub(self, p, q): return self.add(p, self.neg(q))
    def mul(self, p, q):
        if not p or not q: return []
        K = self.K
        res = [K.zero]*(len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                res[i+j] = K.add(res[i+j], K.mul(a, b))
        return self.norm(res)
    def scal(self, c, p): return self.norm([self.K.scal(c, a) for a in p])
    def eq(self, p, q): return self.norm(p) == self.norm(q)
    def iszero(self, p): return not self.norm(p)
    def coef(self, p, d): return p[d] if 0 <= d < len(p) else self.K.zero

def minor(A, drop):
    idx = [i for i in range(len(A)) if i not in drop]
    return [[A[i][j] for j in idx] for i in idx]

def pf(A, K):
    # the recursion of q_pfaffian.md / Pfaffian.pf: along the index 0, sign (-1)^{j'} for j = j'+1
    m = len(A)
    if m == 0: return K.one
    if m % 2 == 1: return K.zero
    tot = K.zero
    for jp in range(m - 1):
        e = A[0][jp+1]
        if K.iszero(e): continue
        t = K.mul(e, pf(minor(A, (0, jp+1)), K))
        tot = K.add(tot, t) if jp % 2 == 0 else K.sub(tot, t)
    return tot

def bmat(a, c, K):
    n = len(a); s = len(c); N = n + s
    B = [[K.zero]*N for _ in range(N)]
    for i in range(n):
        for j in range(n): B[i][j] = a[i][j]
        for k in range(s):
            B[i][n+k] = c[k][i]; B[n+k][i] = K.neg(c[k][i])
    return B
def bpf(a, c, K): return pf(bmat(a, c, K), K)

def det(M, K):
    m = len(M)
    if m == 0: return K.one
    tot = K.zero
    for k in range(m):
        e = M[0][k]
        if K.iszero(e): continue
        sub = [[M[i][j] for j in range(m) if j != k] for i in range(1, m)]
        t = K.mul(e, det(sub, K))
        tot = K.add(tot, t) if k % 2 == 0 else K.sub(tot, t)
    return tot

def kpow(K, a, e):
    res = K.one
    for _ in range(e): res = K.mul(res, a)
    return res

def vand(K, pts):          # prod_{i<j} (pts[j] - pts[i])
    res = K.one
    for i in range(len(pts)):
        for j in range(i+1, len(pts)):
            res = K.mul(res, K.sub(pts[j], pts[i]))
    return res

# ---- the cofactor of the Vandermonde: det(p_k(x_i)) = vand(x) * G(x; p) --------------------------
# p_k: polynomials in T with coefficients in K (lists), x_i in K.
def peval(K, p, x):
    res = K.zero
    for a in reversed(p): res = K.add(K.mul(res, x), a)
    return res
def divdiff(K, p, x0):     # q(T) = (p(T) - p(x0))/(T - x0) = sum_d a_d sum_{u+v=d-1} T^u x0^v
    q = []
    for u in range(len(p) - 1):
        acc = K.zero
        for d in range(u+1, len(p)):
            acc = K.add(acc, K.mul(p[d], kpow(K, x0, d-1-u)))
        q.append(acc)
    return q
def G(K, pts, ps, signed=True):
    m = len(pts)
    if m == 0: return K.one
    x0 = pts[0]
    qs = [divdiff(K, p, x0) for p in ps]
    tot = K.zero
    for k in range(m):
        e = peval(K, ps[k], x0)
        if K.iszero(e): continue
        t = K.mul(e, G(K, pts[1:], [qs[j] for j in range(m) if j != k], signed))
        tot = K.add(tot, t) if (k % 2 == 0 or not signed) else K.sub(tot, t)
    return tot

# =====================================================================================
# (V) Vandermonde divisibility, in the polynomial ring (no box)
# =====================================================================================
for m in range(0, 5):
    K = Box(m, None)
    pts = [K.var(i) for i in range(m)]
    for trial in range(6):
        ps = [[K.const(random.randint(-3, 3)) for _ in range(random.randint(1, 5))] for _ in range(m)]
        M = [[peval(K, ps[k], pts[i]) for k in range(m)] for i in range(m)]
        d = det(M, K)
        check("V m=%d trial=%d" % (m, trial), K.eq(d, K.mul(vand(K, pts), G(K, pts, ps))))
    # monomial columns y^{e_k}
    for trial in range(4):
        es = [random.randint(0, 6) for _ in range(m)]
        ps = [[K.zero]*e + [K.one] for e in es]
        M = [[K.var(i, e) for e in es] for i in range(m)]
        check("V monomials m=%d e=%s" % (m, es), K.eq(det(M, K), K.mul(vand(K, pts), G(K, pts, ps))))
# control: the cofactor without the signs (-1)^k
K = Box(3, None); pts = [K.var(i) for i in range(3)]
fires = 0
for trial in range(10):
    ps = [[K.const(random.randint(-3, 3)) for _ in range(4)] for _ in range(3)]
    M = [[peval(K, ps[k], pts[i]) for k in range(3)] for i in range(3)]
    if not K.eq(det(M, K), K.mul(vand(K, pts), G(K, pts, ps, signed=False))): fires += 1
control("V without the signs (-1)^k: %d/10" % fires, fires > 0)
print("V done", NCHK, NFAIL); sys.stdout.flush()

# =====================================================================================
# The odd box
# =====================================================================================
def Dab(K, q, a, b):       # ColOne.Dab q a b = sum_{u<q-1} (-1)^u a^u b^{q-2-u}
    tot = K.zero
    for u in range(q - 1):
        t = K.mul(kpow(K, a, u), kpow(K, b, q-2-u))
        tot = K.add(tot, t) if u % 2 == 0 else K.sub(tot, t)
    return tot
def omega(K, r, s, a, b):
    tot = K.zero
    for u in range(r):
        if u <= s and s - u < r:
            t = K.mul(kpow(K, a, u), kpow(K, b, s-u))
            tot = K.add(tot, t) if u % 2 == 0 else K.sub(tot, t)
    return tot
def Hm(K, Z, r, ys):       # matrix over K[zeta]
    h = (r - 1)//2; n = len(ys)
    return [[Z.norm([omega(K, r, 2*(h+tau)+1, ys[i], ys[j]) for tau in range(h)]) for j in range(n)] for i in range(n)]
def Ev(K, Z, r, y): return Z.norm([kpow(K, y, 2*al) for al in range((r-1)//2 + 1)])
def Od(K, Z, r, y): return Z.norm([kpow(K, y, 2*be+1) for be in range((r-1)//2)])
def ay(K, r, ys): return [[Dab(K, r, ys[i], ys[j]) for j in range(len(ys))] for i in range(len(ys))]

# (H) Hm(i, j) = C(D(y_i, y_j)) * Od(y_j) in the box
for r in (3, 5, 7, 9):
    K = Box(2, r); Z = Zeta(K); ys = [K.var(0), K.var(1)]
    H = Hm(K, Z, r, ys)
    for (i, j) in ((0, 1), (1, 0), (0, 0)):
        rhs = Z.mul(Z.const(Dab(K, r+1, ys[i], ys[j])), Od(K, Z, r, ys[j]))
        check("H r=%d (%d,%d)" % (r, i, j), Z.eq(H[i][j], rhs))
    # controls
    wrong = Z.mul(Z.const(Dab(K, r+1, ys[0], ys[1])), Od(K, Z, r, ys[0]))
    control("H with Od(y_i) in the place of Od(y_j), r=%d" % r, not Z.eq(H[0][1], wrong))
    K0 = Box(2, None); Z0 = Zeta(K0); y0 = [K0.var(0), K0.var(1)]
    H0 = Hm(K0, Z0, r, y0)
    control("H without the box, r=%d" % r,
            not Z0.eq(H0[0][1], Z0.mul(Z0.const(Dab(K0, r+1, y0[0], y0[1])), Od(K0, Z0, r, y0[1]))))
print("H done", NCHK, NFAIL); sys.stdout.flush()

# perfect matchings of a list T (as lists of pairs (x, z), x < z), with the number of crossings
def matchings(T):
    if not T: yield []; return
    x = T[0]
    for i in range(1, len(T)):
        z = T[i]; rest = T[1:i] + T[i+1:]
        for mm in matchings(rest): yield [(x, z)] + mm
def crossings(mm):
    c = 0
    for (a, b) in mm:
        for (cc, d) in mm:
            if a < cc < b < d: c += 1
    return c

# (P) pf(Hm|_T) = sum over the perfect matchings pi of T of (-1)^cross * prod D(y_x, y_z) * prod Od(y_z)
def pfH_terms(K, Z, r, ys, T):
    # returns the list of (pairs, DQ in K, coefficient in K[zeta])
    out = []
    for mm in matchings(list(T)):
        DQ = K.one; co = Z.one
        for (x, z) in mm:
            DQ = K.mul(DQ, Dab(K, r+1, ys[x], ys[z]))
            co = Z.mul(co, Od(K, Z, r, ys[z]))
        if crossings(mm) % 2 == 1: co = Z.neg(co)
        out.append((mm, DQ, co))
    return out
for (r, n) in ((3, 2), (3, 4), (3, 6), (5, 2), (5, 4), (7, 2), (7, 4)):
    K = Box(n, r); Z = Zeta(K); ys = [K.var(i) for i in range(n)]
    H = Hm(K, Z, r, ys)
    direct = pf(H, Z)
    tot = Z.zero
    for (mm, DQ, co) in pfH_terms(K, Z, r, ys, range(n)):
        tot = Z.add(tot, Z.mul(Z.const(DQ), co))
    check("P r=%d n=%d" % (r, n), Z.eq(direct, tot))
    if n >= 4:
        tot2 = Z.zero
        for (mm, DQ, co) in pfH_terms(K, Z, r, ys, range(n)):
            c2 = co if crossings(mm) % 2 == 0 else Z.neg(co)     # all signs +
            tot2 = Z.add(tot2, Z.mul(Z.const(DQ), c2))
        control("P without the crossing signs, r=%d n=%d" % (r, n), not Z.eq(direct, tot2))
print("P done", NCHK, NFAIL); sys.stdout.flush()

# =====================================================================================
# (M) The certificate of membership.
#   case a: n = s + 2(t+1), borders y^{e_0..e_{s-1}};  Pf(y; c) is, for t+1 <= h,
#           (-1)^{t+1} [zeta^{h-1-t}] bpf(Hm; C c, Ev, Od), and 0 otherwise           (E9, (S5)(a))
#   case b: n = s + 1 + 2t, borders y^{e_0..e_{s-1}}, y^{2h};  for t <= h,
#           (-1)^t [zeta^{h-t}] bpf(Hm; C c, Ev), and 0 otherwise                      (E9, (S5)(b))
#   Laplace (B5): bpf(Hm; c') = sum_S (-1)^{sum S} det(c'_k(S_i)) pf(Hm|_{S^c}),  |S| = s' = #c'
#   (V): det(c'_k(S_i)) = C(Delta(S)) * g_S;   (P): pf(Hm|_T) = sum_Q C(D_Q) * coefficient
#   So Pf = sum_{S,Q} Delta(S) D_Q * (an element of the box ring): a member of the ideal U.
# =====================================================================================
def certificate(r, case, es, t):
    h = (r - 1)//2; s = len(es)
    n = s + 2*(t+1) if case == 'a' else s + 1 + 2*t
    K = Box(n, r); Z = Zeta(K)
    K0 = Box(n, None); Z0 = Zeta(K0)                    # no box, for the divisibility
    ys = [K.var(i) for i in range(n)]; y0 = [K0.var(i) for i in range(n)]
    # left side
    c = [[kpow(K, ys[i], e) for i in range(n)] for e in es]
    if case == 'b': c = c + [[kpow(K, ys[i], 2*h) for i in range(n)]]
    lhs = bpf(ay(K, r, ys), c, K)
    name = "M r=%d case=%s e=%s t=%d n=%d" % (r, case, es, t, n)
    d = h - 1 - t if case == 'a' else h - t
    if d < 0:
        check(name + " (zero case)", K.iszero(lhs))
        return ('zero', n)
    sign = (-1)**(t+1) if case == 'a' else (-1)**t
    # borders over K[zeta], as polynomials in T with coefficients in Z0 = Z[y][zeta]
    def monoT(e): return [Z0.zero]*e + [Z0.one]
    EvT = []; OdT = []
    for al in range(h+1):
        EvT += [Z0.mono(K0.one, al), Z0.zero]
    EvT = EvT[:-1]                                      # sum_al zeta^al T^{2 al}
    for be in range(h):
        OdT += [Z0.zero, Z0.mono(K0.one, be)]           # sum_be zeta^be T^{2 be + 1}
    psT = [monoT(e) for e in es] + [EvT] + ([OdT] if case == 'a' else [])
    sp = len(psT)
    cz = [[Z.const(kpow(K, ys[i], e)) for i in range(n)] for e in es] + [[Ev(K, Z, r, ys[i]) for i in range(n)]]
    if case == 'a': cz = cz + [[Od(K, Z, r, ys[i]) for i in range(n)]]
    H = Hm(K, Z, r, ys)
    # E9 (S5), again, in the box ring
    big = bpf(H, cz, Z)
    check(name + " (S5)", K.eq(lhs, K.scal(sign, Z.coef(big, d))))
    lap = Z.zero; cert = K.zero; nterms = 0
    for S in itertools.combinations(range(n), sp):
        T = [i for i in range(n) if i not in S]
        ptsS0 = [Z0.const(y0[i]) for i in S]
        g0 = G(Z0, ptsS0, psT)                          # in Z[y][zeta]
        detS0 = det([[peval(Z0, psT[k], ptsS0[i]) for k in range(sp)] for i in range(sp)], Z0)
        check(name + " (V) S=%s" % (S,), Z0.eq(detS0, Z0.mul(Z0.const(vand(K0, [y0[i] for i in S])), g0)))
        # reduce g0 and det to the box
        def red(pz): return Z.norm([{k: v for k, v in a.items() if max(k) < r} if a else {} for a in pz])
        gS = red(g0); detS = red(detS0)
        check(name + " det in the box S=%s" % (S,),
              Z.eq(detS, det([[cz[k][i] for k in range(sp)] for i in S], Z)))
        DeltaS = vand(K, [ys[i] for i in S])
        sgS = -1 if sum(S) % 2 else 1
        for (mm, DQ, co) in pfH_terms(K, Z, r, ys, T):
            lap = Z.add(lap, Z.scal(sgS, Z.mul(detS, Z.mul(Z.const(DQ), co))))
            coefSQ = K.scal(sign*sgS, Z.coef(Z.mul(gS, co), d))        # the box element multiplying Delta(S) D_Q
            cert = K.add(cert, K.mul(K.mul(DeltaS, DQ), coefSQ))
            nterms += 1
    check(name + " Laplace", Z.eq(big, lap))
    check(name + " CERTIFICATE", K.eq(lhs, cert))
    return ('cert', n, nterms, len(lhs))

cells = []
# the cases of the paper: l >= 1: e = (0, ..., l-2), case a;  l = 0: case b with no exponent
LIM = 120000
for r in (3, 5, 7, 9, 11):
    h = (r - 1)//2
    for l in range(1, h + 2):
        for t in range(0, h + 1):
            n = (l - 1) + 2*(t + 1)
            if r**n <= LIM and n <= 6: cells.append((r, 'a', tuple(range(l - 1)), t))
    for t in range(0, h + 2):
        n = 1 + 2*t
        if r**n <= LIM: cells.append((r, 'b', (), t))
# more general borders (any exponents): case a and case b
cells += [(3, 'a', (1,), 0), (3, 'a', (2,), 0), (3, 'a', (0, 2), 0), (3, 'b', (0,), 0), (3, 'b', (1,), 1),
          (3, 'b', (0, 1), 1), (3, 'b', (0,), 2),
          (5, 'a', (2,), 0), (5, 'a', (3,), 1), (5, 'a', (1, 3), 0), (5, 'a', (4, 0), 0),
          (5, 'b', (0,), 1), (5, 'b', (1,), 1), (5, 'b', (0, 1), 1), (5, 'b', (3,), 0), (5, 'b', (2, 0), 0),
          (7, 'a', (1,), 0), (7, 'b', (0,), 1), (7, 'b', (2,), 0),
          (7, 'a', (2,), 1), (7, 'a', (1, 4), 0), (7, 'b', (1,), 2), (7, 'b', (0, 3), 1), (9, 'a', (5,), 1),
          (9, 'b', (2,), 1), (9, 'b', (1, 2), 1)]
seen = set()
for cell in cells:
    if cell in seen: continue
    seen.add(cell)
    res = certificate(*cell)
    print("cell", cell, res); sys.stdout.flush()
print("M done", NCHK, NFAIL); sys.stdout.flush()

# =====================================================================================
# (I) Independent test of the statement by linear algebra modulo a prime, in the degree of the
#     target, with controls.  U = ( Delta(S) D_Q : |S| = p, Q a perfect matching of the rest ).
# =====================================================================================
PR = 2147483629
def rank_mod(vecs, monos):
    idx = {m: i for i, m in enumerate(monos)}
    rows = []
    for v in vecs:
        row = {}
        for k, c in v.items():
            c %= PR
            if c: row[idx[k]] = c
        if row: rows.append(row)
    rank = 0; piv = {}
    for row in rows:
        row = dict(row)
        while row:
            lead = min(row)
            if lead in piv:
                pr = piv[lead]; f = row[lead]
                for k, c in pr.items():
                    w = (row.get(k, 0) - f*c) % PR
                    if w: row[k] = w
                    else: row.pop(k, None)
            else:
                inv = pow(row[lead], PR - 2, PR)
                piv[lead] = {k: c*inv % PR for k, c in row.items()}
                rank += 1
                break
    return rank
def gens_U(K, r, ys, p):
    n = len(ys); out = []
    for S in itertools.combinations(range(n), p):
        T = [i for i in range(n) if i not in S]
        DS = vand(K, [ys[i] for i in S])
        for mm in matchings(T):
            g = DS
            for (x, z) in mm: g = K.mul(g, Dab(K, r+1, ys[x], ys[z]))
            out.append(g)
    return out
def degree(p): return sum(next(iter(p)))
def member(K, r, n, gens, target):
    dt = degree(target)
    monos = [m for m in itertools.product(range(r), repeat=n) if sum(m) == dt]
    vecs = []
    for g in gens:
        if not g: continue
        dg = degree(g)
        if dg > dt: continue
        for m in itertools.product(range(r), repeat=n):
            if sum(m) == dt - dg:
                v = K.mul(g, {m: 1})
                if v: vecs.append(v)
    r0 = rank_mod(vecs, monos); r1 = rank_mod(vecs + [target], monos)
    return r0 == r1, r0
for (r, case, es, t) in [(3, 'b', (), 1), (5, 'b', (), 1), (5, 'a', (), 1), (5, 'a', (0,), 0), (5, 'b', (), 2),
                         (7, 'b', (), 1), (7, 'a', (), 1), (5, 'b', (0,), 1), (7, 'a', (0,), 0),
                         (7, 'a', (0,), 1), (7, 'b', (), 2), (9, 'a', (), 1), (9, 'a', (0, 1), 0)]:
    h = (r - 1)//2; s = len(es)
    n = s + 2*(t+1) if case == 'a' else s + 1 + 2*t
    K = Box(n, r); ys = [K.var(i) for i in range(n)]
    c = [[kpow(K, ys[i], e) for i in range(n)] for e in es]
    if case == 'b': c = c + [[kpow(K, ys[i], 2*h) for i in range(n)]]
    lhs = bpf(ay(K, r, ys), c, K)
    p = s + 2 if case == 'a' else s + 1
    gens = gens_U(K, r, ys, p)
    name = "I r=%d case=%s e=%s t=%d n=%d" % (r, case, es, t, n)
    if not lhs:
        check(name + " (target is zero)", True); print(name, "target zero"); continue
    ok, rk = member(K, r, n, gens, lhs)
    check(name, ok)
    dt = degree(lhs)
    nmon = sum(1 for mo in itertools.product(range(r), repeat=n) if sum(mo) == dt)
    print(name, "member:", ok, "rank of U in that degree:", rk, "of", nmon, "generators:", len(gens)); sys.stdout.flush()
    # control 0: the target plus one monomial of its degree (the first one that leaves the ideal, if any)
    fired = False
    for mo in itertools.product(range(r), repeat=n):
        if sum(mo) == dt:
            okq, _ = member(K, r, n, gens, K.add(lhs, {mo: 1}))
            if not okq: fired = True; break
    control(name + " target plus one monomial", fired)
    # control 0': case a, the ideal with p - 2 fixed points (one pair more)
    if case == 'a' and p >= 2:
        gensm = gens_U(K, r, ys, p - 2)
        okm, rkm = member(K, r, n, gensm, lhs)
        control(name + " in the ideal with %d fixed points instead of %d" % (p - 2, p), not okm)
    # control 1: one single term of the Pfaffian (the product of the first matching), when it is not the whole
    # control 2: the ideal with p + 2 fixed points (one pair fewer)
    if n - (p + 2) >= 0:
        gens2 = gens_U(K, r, ys, p + 2)
        ok2, rk2 = member(K, r, n, gens2, lhs)
        control(name + " in the ideal with %d fixed points instead of %d" % (p + 2, p), not ok2)
    # control 3: U with D^- (Dab r) in the place of D (Dab (r+1))
    gens3 = []
    for S in itertools.combinations(range(n), p):
        T = [i for i in range(n) if i not in S]
        DS = vand(K, [ys[i] for i in S])
        for mm in matchings(T):
            g = DS
            for (x, z) in mm: g = K.mul(g, K.mul(Dab(K, r, ys[x], ys[z]), ys[x]))   # y_x D^-: same degree as D
            gens3.append(g)
    if n - p >= 2:
        ok3, rk3 = member(K, r, n, gens3, lhs)
        control(name + " with y_x*D^- in the place of D", not ok3)
print("I done", NCHK, NFAIL)

# =====================================================================================
# (M4) the same on a set B of indices of a larger ring: Pf of (y o iota) lies in U_p(y; B)
# =====================================================================================
for (r, m, B, case, es, t) in [(3, 4, (0, 2, 3), 'b', (), 1), (3, 5, (1, 2, 4), 'b', (), 1),
                               (5, 5, (0, 1, 3, 4), 'a', (), 1), (5, 4, (0, 2, 3), 'b', (), 1),
                               (5, 5, (0, 2, 4), 'a', (0,), 0), (3, 5, (0, 1, 3, 4), 'b', (1,), 1)]:
    h = (r - 1)//2; s = len(es); n = len(B)
    assert n == (s + 2*(t+1) if case == 'a' else s + 1 + 2*t)
    K = Box(m, r); ysB = [K.var(i) for i in B]
    c = [[kpow(K, yy, e) for yy in ysB] for e in es]
    if case == 'b': c = c + [[kpow(K, yy, 2*h) for yy in ysB]]
    lhs = bpf(ay(K, r, ysB), c, K)
    p = s + 2 if case == 'a' else s + 1
    gens = []
    for S in itertools.combinations(B, p):
        T = [i for i in B if i not in S]
        DS = vand(K, [K.var(i) for i in S])
        for mm in matchings(T):
            g = DS
            for (x, z) in mm: g = K.mul(g, Dab(K, r+1, K.var(x), K.var(z)))
            gens.append(g)
    name = "M4 r=%d m=%d B=%s case=%s e=%s t=%d" % (r, m, B, case, es, t)
    if not lhs:
        check(name + " (target is zero)", True); print(name, "target zero"); continue
    ok, rk = member(K, r, m, gens, lhs)
    check(name, ok); print(name, "member:", ok, "rank:", rk, "generators:", len(gens)); sys.stdout.flush()
    # control: the generators built on another set B' of the same size
    Bp = tuple(i for i in range(m) if i not in B)[:1] + B[1:]
    gensp = []
    for S in itertools.combinations(Bp, p):
        T = [i for i in Bp if i not in S]
        DS = vand(K, [K.var(i) for i in S])
        for mm in matchings(T):
            g = DS
            for (x, z) in mm: g = K.mul(g, Dab(K, r+1, K.var(x), K.var(z)))
            gensp.append(g)
    okp, rkp = member(K, r, m, gensp, lhs)
    control(name + " with the ideal of another set B' = %s" % (Bp,), not okp)
print("M4 done", NCHK, NFAIL)
print("TOTAL checks %d failures %d; controls %d fire %d" % (NCHK, NFAIL, NCTL, NCTLFIRE))
