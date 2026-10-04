# chkE16.py — Grepy Mandalay, 3 Oct 2026. Brute force for E16 (q_even_blocks.md):
# the colour reduction for every m (paper v11 §9.3): self-inverse colours (1, and -1 when r' is
# even and p odd), compatible matchings, and Lemma 9.5 (tensor decomposition of pi_c(I)).
# Pure Python + numpy; small finite fields by tables.
import itertools, sys
import numpy as np

NCHK = 0; NFAIL = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        if NFAIL <= 25: print('FAIL', name, flush=True)

# ---------- finite fields F_p and F_{p^2} by tables ----------
class GF:
    def __init__(self, p, n=1, nonres=None):
        self.p, self.n = p, n
        self.Q = p ** n
        if n == 1:
            elems = list(range(p))
            self.add = [[(a + b) % p for b in elems] for a in elems]
            self.mul = [[(a * b) % p for b in elems] for a in elems]
        else:  # F_p[i]/(i^2 - a i - b) given as nonres=(a, b): i^2 = a i + b
            A, B = nonres
            def dec(x): return (x % p, x // p)
            def enc(u, v): return (u % p) + p * (v % p)
            self.add = [[enc(dec(x)[0] + dec(y)[0], dec(x)[1] + dec(y)[1]) for y in range(self.Q)] for x in range(self.Q)]
            def m(x, y):
                a, b = dec(x); c, d = dec(y)
                # (a + b i)(c + d i) = ac + (ad + bc) i + bd i^2
                bd = b * d
                return enc(a * c + bd * B, a * d + b * c + bd * A)
            self.mul = [[m(x, y) for y in range(self.Q)] for x in range(self.Q)]
        self.neg = [next(y for y in range(self.Q) if self.add[x][y] == 0) for x in range(self.Q)]
        self.inv = [None] + [next(y for y in range(self.Q) if self.mul[x][y] == 1) for x in range(1, self.Q)]
        # sanity: field
        for x in range(1, self.Q):
            assert self.inv[x] is not None
    def sub(self, a, b): return self.add[a][self.neg[b]]
    def pw(self, a, e):
        r = 1
        for _ in range(e): r = self.mul[r][a]
        return r
    def from_int(self, z):  # integer -> field (prime subfield)
        z %= self.p
        return z

# ---------- truncated polynomial ring R_c = F[x_1..x_d]/(x_i^q), t_i = c_i + x_i ----------
class Box:
    def __init__(self, F, d, q):
        self.F, self.d, self.q = F, d, q
        self.mons = list(itertools.product(range(q), repeat=d))
        self.idx = {m: i for i, m in enumerate(self.mons)}
        self.N = len(self.mons)
    def zero(self): return {}
    def const(self, a): return {(0,) * self.d: a} if a else {}
    def var(self, i, c):  # t_i = c + x_i
        e = [0] * self.d; e[i] = 1
        r = {tuple(e): 1}
        if c: r[(0,) * self.d] = c
        return r
    def add(self, f, g):
        F = self.F; r = dict(f)
        for m, a in g.items():
            r[m] = F.add[r.get(m, 0)][a]
            if r[m] == 0: del r[m]
        return r
    def scale(self, f, a):
        F = self.F
        return {m: F.mul[a][b] for m, b in f.items() if F.mul[a][b]}
    def mul(self, f, g):
        F = self.F; r = {}
        for m1, a in f.items():
            for m2, b in g.items():
                m = tuple(x + y for x, y in zip(m1, m2))
                if max(m) >= self.q: continue
                v = F.add[r.get(m, 0)][F.mul[a][b]]
                if v: r[m] = v
                elif m in r: del r[m]
        return r
    def vec(self, f):
        v = [0] * self.N
        for m, a in f.items(): v[self.idx[m]] = a
        return v
    def ideal_rows(self, gens):
        rows = []
        for g in gens:
            for mono in self.mons:
                h = {}
                for m, a in g.items():
                    mm = tuple(x + y for x, y in zip(m, mono))
                    if max(mm) < self.q: h[mm] = a
                if h: rows.append(self.vec(h))
        return rows

def rank(F, rows, N):
    if not rows: return 0
    if F.n == 1:
        p = F.p
        M = np.array(rows, dtype=np.int64) % p
        r = 0; nr, nc = M.shape
        for col in range(nc):
            piv = None
            for i in range(r, nr):
                if M[i, col] % p: piv = i; break
            if piv is None: continue
            M[[r, piv]] = M[[piv, r]]
            inv = pow(int(M[r, col]), p - 2, p)
            M[r] = (M[r] * inv) % p
            nzr = np.nonzero(M[:, col] % p)[0]
            for i in nzr:
                if i != r: M[i] = (M[i] - M[i, col] * M[r]) % p
            r += 1
            if r == nr: break
        return r
    # extension field: incremental echelon
    basis = {}
    for row in rows:
        v = list(row)
        while True:
            lead = next((j for j, x in enumerate(v) if x), None)
            if lead is None: break
            if lead not in basis:
                inv = F.inv[v[lead]]
                basis[lead] = [F.mul[inv][x] for x in v]
                break
            b = basis[lead]; a = v[lead]
            v = [F.sub(x, F.mul[a][y]) for x, y in zip(v, b)]
    return len(basis)

# ---------- matchings ----------
def matchings(pts):
    pts = list(pts)
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        b = pts[i]; rest = pts[1:i] + pts[i + 1:]
        for M in matchings(rest): yield [(a, b)] + M

def perfmatch_count(n):
    if n % 2: return 0
    r = 1
    for j in range(n - 1, 0, -2): r *= j
    return r

def bijections(A, B):
    if len(A) != len(B): return
    for perm in itertools.permutations(B): yield list(zip(A, perm))

# ---------- the cell ----------
def run_cell(F, k, m, p, q, rp, mu, label):
    d = 2 * k + 1; V = list(range(2 * k + 2))
    box = Box(F, d, q)
    one = 1; mone = F.neg[1]
    sinv = [z for z in mu if F.inv[z] == z]
    others = [z for z in mu if F.inv[z] != z]
    R = []
    for z in others:
        if z not in R and F.inv[z] not in R: R.append(z)
    # (A1)
    check(f'{label} 1 in SInv', one in sinv)
    check(f'{label} SInv <= {{1,-1}}', all(z in (one, mone) for z in sinv))
    exp_sinv = {one, mone} if (rp % 2 == 0 and p != 2) else {one}
    check(f'{label} SInv shape', set(sinv) == exp_sinv)
    tot = 0; ctrl = {'drop_minus_block': 0, 'count_wo_minus': 0, 'swap_rule': 0}
    allM = list(matchings(V))
    for c in itertools.product(mu, repeat=d):
        prodc = 1
        for z in c: prodc = F.mul[prodc][z]
        c0 = F.inv[prodc]
        cx = [c0] + list(c)  # colour of every point of V
        cls = {z: [v for v in V if cx[v] == z] for z in mu}
        # (A5) pairs with product 1
        for a, b in itertools.combinations(V, 2):
            lhs = F.mul[cx[a]][cx[b]] == 1
            rhs = any(a in cls[z] and b in cls[z] for z in sinv) or any(
                (a in cls[z] and b in cls[F.inv[z]]) or (b in cls[z] and a in cls[F.inv[z]]) for z in R)
            check(f'{label} A5', lhs == rhs)
        compat = [M for M in allM if all(F.mul[cx[a]][cx[b]] == 1 for a, b in M)]
        exists = all(len(cls[z]) % 2 == 0 for z in sinv) and all(len(cls[z]) == len(cls[F.inv[z]]) for z in R)
        check(f'{label} A8 exists', (len(compat) > 0) == exists)
        if exists:
            cnt = 1
            for z in sinv: cnt *= perfmatch_count(len(cls[z]))
            for z in R:
                f_ = 1
                for j in range(1, len(cls[z]) + 1): f_ *= j
                cnt *= f_
            check(f'{label} A8 count', len(compat) == cnt)
            cnt2 = perfmatch_count(len(cls[one]))
            for z in R:
                f_ = 1
                for j in range(1, len(cls[z]) + 1): f_ *= j
                cnt2 *= f_
            if mone in sinv and cnt2 != len(compat): ctrl['count_wo_minus'] += 1
        # (A6) compatible iff classes mapped right
        for M in allM:
            Jm = {}
            for a, b in M: Jm[a] = b; Jm[b] = a
            comp = all(F.mul[cx[a]][cx[b]] == 1 for a, b in M)
            maps = all(sorted(Jm[v] for v in cls[z]) == cls[z] for z in sinv) and all(
                sorted(Jm[v] for v in cls[z]) == cls[F.inv[z]] for z in R)
            check(f'{label} A6', comp == maps)
            if mone in sinv and cls[mone] and cls[one]:
                wrong = all(sorted(Jm[v] for v in cls[mone]) == cls[one] for _ in [0])
                if wrong != comp: ctrl['swap_rule'] += 1
        # pi_c(psi_J) for all J
        tvar = [None] + [box.var(i, c[i]) for i in range(d)]  # t_a for a = 1..d
        def phi(u):
            s = box.const(1); pw = box.const(1)
            for _ in range(1, m):
                pw = box.mul(pw, u); s = box.add(s, pw)
            return s
        def pairF(a, b):  # a < b
            tb_1 = box.add(tvar[b], box.const(F.neg[1]))
            if a == 0: return tb_1
            u = box.mul(tvar[a], tvar[b])
            return box.mul(tb_1, phi(u))
        gens = []
        for M in allM:
            g = box.const(1)
            for a, b in M:
                a, b = min(a, b), max(a, b)
                g = box.mul(g, pairF(a, b))
            gens.append(g)
        dimI = rank(F, box.ideal_rows(gens), box.N)
        tot += dimI
        if not exists:
            check(f'{label} B1 zero', dimI == 0)
            continue
        # block ideals in their own boxes (variables of the block minus 0)
        def block_dim(points, gen_pairs_list):
            W = [v for v in points if v != 0]
            bb = Box(F, len(W), q)
            pos = {v: j for j, v in enumerate(W)}
            tv = {v: bb.var(pos[v], c[v - 1]) for v in W}
            def phib(u):
                s = bb.const(1); pw = bb.const(1)
                for _ in range(1, m):
                    pw = bb.mul(pw, u); s = bb.add(s, pw)
                return s
            def pf(a, b):
                tb_1 = bb.add(tv[b], bb.const(F.neg[1]))
                if a == 0: return tb_1
                return bb.mul(tb_1, phib(bb.mul(tv[a], tv[b])))
            gs = []
            for pairs in gen_pairs_list:
                g = bb.const(1)
                for a, b in pairs:
                    g = bb.mul(g, pf(min(a, b), max(a, b)))
                gs.append(g)
            if not W:  # empty block: the ideal is F (one generator 1) or 0
                return 1 if any(gs) else 0
            return rank(F, bb.ideal_rows(gs), bb.N)
        dims = {}
        for z in sinv:
            dims[('S', z)] = block_dim(cls[z], list(matchings(cls[z])))
        for z in R:
            dims[('P', z)] = block_dim(cls[z] + cls[F.inv[z]], list(bijections(cls[z], cls[F.inv[z]])))
        prod = 1
        for v in dims.values(): prod *= v
        check(f'{label} B3 dim = product c={cx}', dimI == prod)
        if mone in sinv and cls[mone] and dims[('S', mone)] != 1:
            prod2 = prod // dims[('S', mone)] if dims[('S', mone)] else 0
            if prod2 != dimI: ctrl['drop_minus_block'] += 1
    return tot, ctrl

cells = []
F3 = GF(3); F5 = GF(5); F2 = GF(2)
F9 = GF(3, 2, nonres=(0, 2))   # i^2 = 2 = -1
F4 = GF(2, 2, nonres=(1, 1))   # i^2 = i + 1
def roots(F, r):
    return [x for x in range(1, F.Q) if F.pw(x, r) == 1]

ok_cells = []
for (F, k, m, p, q, rp, Qexp, label) in [
        (F3, 1, 6, 3, 3, 2, 61, 'k1 m6 p3'),
        (F4, 1, 6, 2, 2, 3, 61, 'k1 m6 p2'),
        (F5, 1, 10, 5, 5, 2, 217, 'k1 m10 p5'),
        (F9, 1, 12, 3, 3, 4, 331, 'k1 m12 p3'),
        (F4, 1, 12, 2, 4, 3, 331, 'k1 m12 p2'),
        (F5, 1, 20, 5, 5, 4, 1027, 'k1 m20 p5'),
        (F3, 2, 6, 3, 3, 2, 1001, 'k2 m6 p3'),
    ]:
    mu = roots(F, rp)
    check(f'{label} |mu| = r', len(mu) == rp)
    tot, ctrl = run_cell(F, k, m, p, q, rp, mu, label)
    check(f'{label} sum dim pi_c(I) = Q_k(m) = {Qexp} (got {tot})', tot == Qexp)
    print(f'{label}: sum = {tot} (expect {Qexp}), checks {NCHK}, fails {NFAIL}, controls {ctrl}', flush=True)
    ok_cells.append((label, ctrl))
print('checks', NCHK, 'failures', NFAIL)
fired = {key: sum(c[key] for _, c in ok_cells) for key in ['drop_minus_block', 'count_wo_minus', 'swap_rule']}
print('controls fired (each must be > 0):', fired)
print('FIN-OK' if NFAIL == 0 and all(v > 0 for v in fired.values()) else 'FIN-WITH-PROBLEMS')
