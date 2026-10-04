# chkE9.py — brute force for Lean piece E9 (q_rank_two.md): the rank-two update of a bordered
# Pfaffian and the closed forms of the odd box (paper v11 §8.5, Lemma 8.8 and Corollary 8.9, in
# Pfaffian form, without the exterior algebra).
# Grepy Mandalay, 2 Oct 2026. Exact integer arithmetic, no external library.
# Polynomials in zeta are lists of integers (coefficient of zeta^i at place i).
import random, sys
random.seed(2026100209)
NCHK = 0; NFAIL = 0; CTRL = {}
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        print('FAIL', name); sys.stdout.flush()
def control(name, fires):
    # a control is a WRONG statement: it must fail on the data (fires = True) at least once
    a, b = CTRL.get(name, (0, 0))
    CTRL[name] = (a + (1 if fires else 0), b + 1)

# ---------- polynomials in zeta ----------
def pnorm(p):
    p = list(p)
    while p and p[-1] == 0: p.pop()
    return p
def padd(p, q):
    n = max(len(p), len(q)); r = [0]*n
    for i, v in enumerate(p): r[i] += v
    for i, v in enumerate(q): r[i] += v
    return pnorm(r)
def pneg(p): return [-v for v in p]
def psub(p, q): return padd(p, pneg(q))
def pmul(p, q):
    if not p or not q: return []
    r = [0]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q): r[i+j] += a*b
    return pnorm(r)
def pconst(c): return pnorm([c])
def pmono(c, d): return pnorm([0]*d + [c])
def ppow(p, e):
    r = [1]
    for _ in range(e): r = pmul(r, p)
    return r
def pcoef(p, d): return p[d] if 0 <= d < len(p) else 0
def pdeg(p): return len(p) - 1   # -1 for the zero polynomial

class Ring:      # integers
    zero = 0; one = 1
    add = staticmethod(lambda a, b: a+b); mul = staticmethod(lambda a, b: a*b)
    neg = staticmethod(lambda a: -a); iszero = staticmethod(lambda a: a == 0)
class PRing:     # Z[zeta]
    zero = []; one = [1]
    add = staticmethod(padd); mul = staticmethod(pmul)
    neg = staticmethod(pneg); iszero = staticmethod(lambda a: not a)

def pf(A, K):
    # the recursion of q_pfaffian.md along the index 0
    m = len(A)
    if m == 0: return K.one
    if m % 2: return K.zero
    tot = K.zero
    for j in range(1, m):
        if K.iszero(A[0][j]): continue
        idx = [i for i in range(m) if i not in (0, j)]
        t = K.mul(A[0][j], pf([[A[a][b] for b in idx] for a in idx], K))
        tot = K.add(tot, t if (j+1) % 2 == 0 else K.neg(t))
    return tot
def bmat(a, c, K):
    n = len(a); s = len(c)
    B = [[K.zero]*(n+s) for _ in range(n+s)]
    for i in range(n):
        for j in range(n): B[i][j] = a[i][j]
        for k in range(s):
            B[i][n+k] = c[k][i]; B[n+k][i] = K.neg(c[k][i])
    return B
def bpf(a, c, K): return pf(bmat(a, c, K), K)

def randalt(n, lo=-4, hi=4):
    a = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            v = random.randint(lo, hi); a[i][j] = v; a[j][i] = -v
    return a
def randcol(n, lo=-3, hi=3): return [random.randint(lo, hi) for _ in range(n)]
def randpoly(d): return pnorm([random.randint(-3, 3) for _ in range(d+1)])
def randaltpoly(n, d):
    a = [[[] for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            v = randpoly(d); a[i][j] = v; a[j][i] = pneg(v)
    return a

# =====================================================================================
# Part R: general, over a commutative ring
# =====================================================================================
# (R1) elementary operation: A'(i,j) = A(i,j) + lam*([i=w]A(x,j) + [j=w]A(i,x)), x != w.
for m in range(2, 8):
    for rep in range(12):
        A = randalt(m); x = random.randrange(m); w = random.choice([i for i in range(m) if i != x])
        lam = random.randint(-3, 3)
        A1 = [[A[i][j] + lam*((A[x][j] if i == w else 0) + (A[i][x] if j == w else 0)) for j in range(m)] for i in range(m)]
        check('R1 alt', all(A1[i][i] == 0 for i in range(m)) and all(A1[j][i] == -A1[i][j] for i in range(m) for j in range(m)))
        check('R1', pf(A1, Ring) == pf(A, Ring))
        # control: change only the row, not the column (not alternating in general; pf differs)
        A2 = [[A[i][j] + lam*(A[x][j] if i == w else 0) for j in range(m)] for i in range(m)]
        if m % 2 == 0 and lam != 0: control('R1 row only', pf(A2, Ring) != pf(A, Ring))

# (R2) border shift: a'(i,j) = a(i,j) + lam_i c_k(j) - lam_j c_k(i)
for n in range(1, 7):
    for s in range(1, n+1):
        if (n+s) % 2: continue
        for rep in range(8):
            a = randalt(n); c = [randcol(n) for _ in range(s)]; k = random.randrange(s); lam = randcol(n)
            a1 = [[a[i][j] + lam[i]*c[k][j] - lam[j]*c[k][i] for j in range(n)] for i in range(n)]
            check('R2', bpf(a1, c, Ring) == bpf(a, c, Ring))
            # control: a column that is NOT a border
            e = randcol(n)
            a2 = [[a[i][j] + lam[i]*e[j] - lam[j]*e[i] for j in range(n)] for i in range(n)]
            if n > s: control('R2 not a border', bpf(a2, c, Ring) != bpf(a, c, Ring))

# (R3) homogeneity: bpf(t a; c) = t^kappa bpf(a; c), n = s + 2 kappa
for n in range(0, 7):
    for s in range(0, n+1):
        if (n+s) % 2: continue
        kappa = (n-s)//2
        for rep in range(5):
            a = randalt(n); c = [randcol(n) for _ in range(s)]; t = random.choice([-3, -2, 2, 3])
            ta = [[t*a[i][j] for j in range(n)] for i in range(n)]
            check('R3', bpf(ta, c, Ring) == t**kappa * bpf(a, c, Ring))
            if kappa >= 1 and bpf(a, c, Ring) != 0:
                control('R3 exponent n', bpf(ta, c, Ring) != t**n * bpf(a, c, Ring))

# (R4) rank-two update: a'(i,j) = a(i,j) - (E_i O_j - E_j O_i):
#      bpf(a'; c) = bpf(a; c) + bpf(a; c, E, O)      (E, O appended as the last two borders, in this order)
for n in range(0, 8):
    for s in range(0, n+1):
        if (n+s) % 2: continue
        for rep in range(8 if n < 7 else 3):
            a = randalt(n); c = [randcol(n) for _ in range(s)]; E = randcol(n); O = randcol(n)
            a1 = [[a[i][j] - (E[i]*O[j] - E[j]*O[i]) for j in range(n)] for i in range(n)]
            x = bpf(a, c, Ring); y = bpf(a, c + [E, O], Ring)
            check('R4', bpf(a1, c, Ring) == x + y)
            if y != 0:
                control('R4 minus', bpf(a1, c, Ring) != x - y)
                control('R4 order O,E', bpf(a1, c, Ring) != x + bpf(a, c + [O, E], Ring))
            # equivalent form: a + (E O^T - O E^T) gives x - y
            a3 = [[a[i][j] + (E[i]*O[j] - E[j]*O[i]) for j in range(n)] for i in range(n)]
            check('R4 plus form', bpf(a3, c, Ring) == x - y)

# (R4') one more border E, the matrix changed by lam_i E_j - lam_j E_i: nothing changes (case of R2 used below)
# (R5) top coefficient: entries of a of degree <= d, border k of degree <= d_k, n = s + 2 kappa:
#      bpf(a; c) has degree <= kappa d + sum d_k and its coefficient there is bpf(top a; top c)
for n in range(0, 6):
    for s in range(0, n+1):
        if (n+s) % 2: continue
        kappa = (n-s)//2
        for rep in range(5):
            d = random.randint(0, 2); dk = [random.randint(0, 2) for _ in range(s)]
            a = randaltpoly(n, d); c = [[randpoly(dk[k]) for _ in range(n)] for k in range(s)]
            P = bpf(a, c, PRing); N = kappa*d + sum(dk)
            check('R5 degree', pdeg(P) <= N)
            atop = [[pcoef(a[i][j], d) for j in range(n)] for i in range(n)]
            ctop = [[pcoef(c[k][i], dk[k]) for i in range(n)] for k in range(s)]
            check('R5 top', pcoef(P, N) == bpf(atop, ctop, Ring))
            if kappa >= 1 and d >= 1:
                alow = [[pcoef(a[i][j], 0) for j in range(n)] for i in range(n)]
                if bpf(atop, ctop, Ring) != bpf(alow, ctop, Ring):
                    control('R5 constant terms', pcoef(P, N) != bpf(alow, ctop, Ring))

# =====================================================================================
# Part S: the odd box. r = 2h+1.
# =====================================================================================
def omega(r, s, a, b):
    return sum((-1)**u * a**u * b**(s-u) for u in range(r) if 0 <= s-u <= r-1)
def Dab(q, a, b):
    return sum((-1)**u * a**u * b**(q-2-u) for u in range(q-1))

# two-variable truncated polynomials, for (S3): dict {(i,j): coef}, modulo a^r, b^r
def tmul(p, q, r):
    out = {}
    for (i, j), u in p.items():
        for (k, l), v in q.items():
            if i+k < r and j+l < r:
                out[(i+k, j+l)] = out.get((i+k, j+l), 0) + u*v
    return {k: v for k, v in out.items() if v}
def t_omega(r, s):
    out = {}
    for u in range(r):
        if 0 <= s-u <= r-1: out[(u, s-u)] = (-1)**u
    return out
def t_D(r):   # Dab (r+1) a b = sum_{u<r} (-1)^u a^u b^{r-1-u}
    return {(u, r-1-u): (-1)**u for u in range(r)}

for r in (3, 5, 7, 9):
    h = (r-1)//2
    # (S0) antisymmetry of omega_s for odd s, and omega_s(a,a) = 0
    for s in range(1, 2*r-2, 2):
        for rep in range(4):
            a = random.randint(-5, 5); b = random.randint(-5, 5)
            check('S0 antisym', omega(r, s, b, a) == -omega(r, s, a, b))
            check('S0 diag', omega(r, s, a, a) == 0)
    # (S1) omega_{r-2} = Dab r = D^-
    for rep in range(10):
        a = random.randint(-5, 5); b = random.randint(-5, 5)
        check('S1', omega(r, r-2, a, b) == Dab(r, a, b))
        if a != 0 and b != 0 and omega(r, r-2, a, b) != Dab(r+1, a, b): control('S1 with D', True)
    # (S2) sum_{sigma=0}^{2h-1} zeta^sigma omega_{2 sigma+1}(a,b) = Ev(a) Od(b) - Ev(b) Od(a)
    for rep in range(10):
        a = random.randint(-4, 4); b = random.randint(-4, 4)
        lhs = pnorm([omega(r, 2*sg+1, a, b) for sg in range(2*h)])
        Ev = lambda x: pnorm([x**(2*i) for i in range(h+1)])
        Od = lambda x: pnorm([x**(2*i+1) for i in range(h)])
        rhs = psub(pmul(Ev(a), Od(b)), pmul(Ev(b), Od(a)))
        check('S2', lhs == rhs)
        rhs_bad = padd(pmul(Ev(a), Od(b)), pmul(Ev(b), Od(a)))
        if rhs_bad != rhs: control('S2 plus', lhs != rhs_bad)
    # (S3) for odd i, 1 <= i <= r-2: omega_{r-1+i}(a,b) = b^i D(a,b) modulo (a^r, b^r)
    for i in range(1, r-1, 2):
        lhs = t_omega(r, r-1+i)
        rhs = tmul({(0, i): 1}, t_D(r), r)
        check('S3', lhs == rhs)
        rhs2 = tmul({(i, 0): -1}, t_D(r), r)      # and = -a^i D(a,b)
        check('S3 a-form', lhs == rhs2)
        control('S3 low omega', t_omega(r, r-1-i) != tmul({(0, i): 1}, t_D(r), r))

def Wmat(r, sg, y):
    n = len(y)
    return [[omega(r, 2*sg+1, y[i], y[j]) for j in range(n)] for i in range(n)]
def Lmat(r, y):     # sum_{sigma<h} zeta^sigma W_sigma
    h = (r-1)//2; n = len(y)
    return [[pnorm([omega(r, 2*sg+1, y[i], y[j]) for sg in range(h)]) for j in range(n)] for i in range(n)]
def Hmat(r, y):     # sum_{sigma=h}^{2h-1} zeta^{sigma-h} W_sigma
    h = (r-1)//2; n = len(y)
    return [[pnorm([omega(r, 2*sg+1, y[i], y[j]) for sg in range(h, 2*h)]) for j in range(n)] for i in range(n)]
def Evcol(r, y):
    h = (r-1)//2
    return [pnorm([x**(2*i) for i in range(h+1)]) for x in y]
def Odcol(r, y):
    h = (r-1)//2
    return [pnorm([x**(2*i+1) for i in range(h)]) for x in y]
def scal(p, M): return [[pmul(p, e) for e in row] for row in M]
def constcols(c): return [[pconst(v) for v in col] for col in c]

for r in (3, 5, 7):
    h = (r-1)//2
    mzh = pmono(-1, h)                    # -zeta^h
    for n in range(0, 7):
        for s in range(0, n+1):
            reps = 3 if n <= 5 else 1
            for rep in range(reps):
                y = [random.randint(-3, 3) for _ in range(n)]
                c = [randcol(n) for _ in range(s)]; cc = constcols(c)
                L = Lmat(r, y); H = Hmat(r, y); E = Evcol(r, y); O = Odcol(r, y)
                mH = scal(mzh, H)
                # (S4)(i): bpf(L; c) = bpf(-zeta^h H; c) - bpf(-zeta^h H; c, E, O), all n, s
                if (n+s) % 2 == 0:
                    lhs = bpf(L, cc, PRing)
                    rhs = psub(bpf(mH, cc, PRing), bpf(mH, cc + [E, O], PRing))
                    check('S4i', lhs == rhs)
                    kappa = (n-s)//2
                    # homogeneous form, kappa >= 1
                    if kappa >= 1:
                        rhs2 = psub(pmul(ppow(mzh, kappa), bpf(H, cc, PRing)),
                                    pmul(ppow(mzh, kappa-1), bpf(H, cc + [E, O], PRing)))
                        check('S4i hom', lhs == rhs2)
                        bad = padd(pmul(ppow(mzh, kappa), bpf(H, cc, PRing)),
                                   pmul(ppow(mzh, kappa-1), bpf(H, cc + [E, O], PRing)))
                        if bad != rhs2: control('S4i plus', lhs != bad)
                    # (S5)(a): n = s + 2(t+1): Pf(y; c) = bpf(W_{h-1}; c) = (-1)^{t+1} coeff_{h-1-t} bpf(H; c, E, O)
                    if kappa >= 1:
                        t = kappa - 1
                        Pfy = bpf(Wmat(r, h-1, y), c, Ring)
                        Q = bpf(H, cc + [E, O], PRing)
                        val = (-1)**(t+1) * pcoef(Q, h-1-t) if t <= h-1 else 0
                        check('S5a', Pfy == val)
                        check('S5a is D^-', Wmat(r, h-1, y) == [[Dab(r, y[i], y[j]) for j in range(n)] for i in range(n)])
                        if Pfy != 0:
                            control('S5a sign', Pfy != (-1)**t * pcoef(Q, h-1-t))
                            control('S5a coefficient h-t', Pfy != (-1)**(t+1) * pcoef(Q, h-t))
                # (S4) with borders that are polynomials in zeta (the statement is for any borders over A[zeta])
                cp = [[randpoly(1) for _ in range(n)] for _ in range(s)]
                if (n+s) % 2 == 0:
                    check('S4i poly borders', bpf(L, cp, PRing) == psub(bpf(mH, cp, PRing), bpf(mH, cp + [E, O], PRing)))
                else:
                    check('S4ii poly borders', bpf(L, cp + [E], PRing) == bpf(mH, cp + [E], PRing))
                # (S4)(ii): bpf(L; c, E) = bpf(-zeta^h H; c, E), all n, s
                if (n+s+1) % 2 == 0:
                    lhs = bpf(L, cc + [E], PRing); rhs = bpf(mH, cc + [E], PRing)
                    check('S4ii', lhs == rhs)
                    # (S5)(b): n = s + 1 + 2t: bpf(W_{h-1}; c, y^{2h}) = (-1)^t coeff_{h-t} bpf(H; c, E)
                    t = (n-s-1)//2
                    if n >= s+1:
                        top = [x**(2*h) for x in y]
                        Pfy = bpf(Wmat(r, h-1, y), c + [top], Ring)
                        Q = bpf(H, cc + [E], PRing)
                        val = (-1)**t * pcoef(Q, h-t) if t <= h else 0
                        check('S5b', Pfy == val)
                        if Pfy != 0:
                            control('S5b sign', Pfy != (-1)**(t+1) * pcoef(Q, h-t))
                            control('S5b with O', Pfy != (-1)**t * pcoef(bpf(H, cc + [O], PRing), h-t))

# the two cases of the paper, with the borders E_l: l >= 1: c = (y^0, ..., y^{l-2}); l = 0: c = (), last border y^{r-1}
for r in (3, 5, 7):
    h = (r-1)//2
    for l in range(0, 5):
        for t in range(0, 3):
            n = l + 1 + 2*t
            if n > 7: continue
            y = [random.randint(-3, 3) for _ in range(n)]
            H = Hmat(r, y); E = Evcol(r, y); O = Odcol(r, y)
            if l >= 1:
                c = [[x**e for x in y] for e in range(l-1)]
                Pfy = bpf(Wmat(r, h-1, y), c, Ring)
                Q = bpf(H, constcols(c) + [E, O], PRing)
                check('paper l>=1', Pfy == ((-1)**(t+1) * pcoef(Q, h-1-t) if t <= h-1 else 0))
            else:
                c = [[x**(r-1) for x in y]]
                Pfy = bpf(Wmat(r, h-1, y), c, Ring)
                Q = bpf(H, [E], PRing)
                check('paper l=0', Pfy == ((-1)**t * pcoef(Q, h-t) if t <= h else 0))

print('checks', NCHK, 'failures', NFAIL)
for k in sorted(CTRL): print('control', k, ': fires', CTRL[k][0], 'of', CTRL[k][1])
print('CHK-E9-END')
