#!/usr/bin/env python3
"""Gate of the printed text of v12 (new statements of §8.3, §8.5, §1.3, §9).
Exact integer / polynomial arithmetic (sympy). Estimate written before the run:
< 300 MB, < 300 s. Grepy Mandalay, 4 Oct 2026."""
import itertools, random, sys, math
import sympy as sp

random.seed(20261004)
FAILS = 0; CHECKS = 0
def check(cond, msg):
    global FAILS, CHECKS
    CHECKS += 1
    if not cond:
        FAILS += 1; print("FAIL", msg)

# ---------- Pfaffians ----------
def matchings(idx):
    if not idx: yield []; return
    a = idx[0]
    for j in range(1, len(idx)):
        b = idx[j]; rest = idx[1:j] + idx[j+1:]
        for m in matchings(rest): yield [(a, b)] + m

def sign_of_listing(lst, order):
    pos = {x: i for i, x in enumerate(order)}
    perm = [pos[x] for x in lst]
    inv = sum(1 for i in range(len(perm)) for j in range(i+1, len(perm)) if perm[i] > perm[j])
    return -1 if inv % 2 else 1

def pf(A, order=None):
    """Definition of §8.3: sum over matchings, sign of the listing permutation."""
    n = len(A)
    idx = list(range(n)) if order is None else order
    if n % 2: return 0
    tot = 0
    for m in matchings(list(range(n))):
        lst = []
        for (a, b) in m: lst += [a, b]
        sgn = sign_of_listing(lst, list(range(n)))
        prod = 1
        for (a, b) in m: prod = prod * A[a][b]
        tot = tot + sgn * prod
    return sp.expand(tot)

def rand_alt(n, lo=-5, hi=5):
    A = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            v = random.randint(lo, hi); A[i][j] = v; A[j][i] = -v
    return A

def minor(A, keep):
    return [[A[i][j] for j in keep] for i in keep]

def bordered(a, cols):
    n = len(a); s = len(cols); M = [[0]*(n+s) for _ in range(n+s)]
    for i in range(n):
        for j in range(n): M[i][j] = a[i][j]
    for k, c in enumerate(cols):
        for i in range(n):
            M[i][n+k] = c[i]; M[n+k][i] = -c[i]
    return M

def bpf(a, cols): return pf(bordered(a, cols))

# (iii) explicit ε, and the matching definition = crossing-sign definition
for n in (2, 4, 6):
    for _ in range(4):
        A = rand_alt(n); P = pf(A)
        for x in range(n):
            tot = 0
            for z in range(n):
                if z == x: continue
                e = (-1)**(x+z+1) if x < z else (-1)**(x+z)
                keep = [i for i in range(n) if i not in (x, z)]
                tot += e * A[x][z] * pf(minor(A, keep))
            check(tot == P, f"(iii) n={n} x={x}")

# (ii) equal rows give 0
for n in (4, 6):
    for _ in range(3):
        A = rand_alt(n); x, w = 0, n-1
        # make rows w and x equal: A[w][k]=A[x][k] for k not in {x,w}, A[x][w]=0
        for k in range(n):
            if k in (x, w): continue
            A[w][k] = A[x][k]; A[k][w] = -A[w][k]
        A[x][w] = 0; A[w][x] = 0
        check(pf(A) == 0, f"(ii) n={n}")

# (F2) last border, (F3), (F4), (F7)
def rc(n): return [random.randint(-4, 4) for _ in range(n)]
for (n, s) in [(1,1),(2,2),(3,1),(3,3),(4,2),(5,1),(5,3),(4,4),(6,2)]:
    for _ in range(3):
        a = rand_alt(n); cols = [rc(n) for _ in range(s)]
        P = bpf(a, cols)
        # (F2)
        tot = 0
        for b in range(n):
            keep = [i for i in range(n) if i != b]
            tot += (-1)**(n+s+b) * cols[-1][b] * bpf(minor(a, keep), [[c[i] for i in keep] for c in cols[:-1]])
        check(tot == P, f"(F2) n={n} s={s}")
        # (F4) expansion along x
        for x in range(n):
            keep = [i for i in range(n) if i != x]
            ax = [a[x][i] for i in keep]
            t1 = (-1)**(x+n+s) * bpf(minor(a, keep), [[c[i] for i in keep] for c in cols] + [ax])
            t2 = 0
            for k in range(1, s+1):
                rest = [cols[j] for j in range(s) if j != k-1]
                t2 += (-1)**(x+n+k) * cols[k-1][x] * bpf(minor(a, keep), [[c[i] for i in keep] for c in rest])
            check(t1 + t2 == P, f"(F4) n={n} s={s} x={x}")
        # (F7) Laplace
        if (n - s) % 2 == 0:
            tot = 0
            for S in itertools.combinations(range(n), s):
                comp = [i for i in range(n) if i not in S]
                sg = (-1)**(sum(S) - s*(s-1)//2)
                d = sp.Matrix([[cols[k][i] for k in range(s)] for i in S]).det() if s else 1
                tot += sg * d * pf(minor(a, comp))
            check((-1)**(s*(s-1)//2) * tot == P, f"(F7) n={n} s={s}")
        # (F3)
        if n == s:
            d = sp.Matrix([[cols[k][i] for k in range(s)] for i in range(n)]).det()
            check(P == (-1)**(s*(s-1)//2) * d, f"(F3) n={n}")

# ---------- §8.5 ----------
z = sp.Symbol('z')  # the formal variable ζ
def omega(s, a, b, r):
    return sum((-1)**u * a**u * b**(s-u) for u in range(r) if 0 <= s-u <= r-1)

def D(a, b, r):  return sum((-1)**u * a**u * b**(r-1-u) for u in range(r))
def Dm(a, b, r): return sum((-1)**u * a**u * b**(r-2-u) for u in range(r-1))

A_, B_ = sp.symbols('a b')
for h in (1, 2, 3, 4):
    r = 2*h+1
    Ev = lambda x: sum(z**al * x**(2*al) for al in range(h+1))
    Od = lambda x: sum(z**be * x**(2*be+1) for be in range(h))
    lhs = sum(z**sg * omega(2*sg+1, A_, B_, r) for sg in range(2*h))
    check(sp.expand(lhs - (Ev(A_)*Od(B_) - Ev(B_)*Od(A_))) == 0, f"(8.6) h={h}")
    check(sp.expand(omega(r-2, A_, B_, r) - Dm(A_, B_, r)) == 0, f"omega_(r-2)=D- h={h}")
    for i in range(1, r-1, 2):
        diff = sp.Poly(sp.expand(omega(r-1+i, A_, B_, r) - B_**i * D(A_, B_, r)), A_, B_)
        ok = all(e[0] >= r or e[1] >= r for e, c in diff.terms())
        check(ok, f"omega_(r-1+i)=b^i D mod box h={h} i={i}")
    check(sp.expand(omega(3, A_, B_, r) + omega(3, B_, A_, r)) == 0, f"antisym h={h}")

# Lemma 8.8 (i), (ii) on random integer data
for (n, s) in [(2,0),(3,1),(4,0),(4,2),(5,1),(6,0),(5,3),(6,2)]:
    for _ in range(3):
        a = rand_alt(n); cols = [rc(n) for _ in range(s)]; E = rc(n); O = rc(n)
        M = [[E[i]*O[j] - O[i]*E[j] for j in range(n)] for i in range(n)]
        aM = [[a[i][j] + M[i][j] for j in range(n)] for i in range(n)]
        check(bpf(aM, cols) == bpf(a, cols) - bpf(a, cols + [E, O]), f"8.8(ii) n={n} s={s}")
        if s >= 1:
            k = random.randrange(s); lam = rc(n)
            ap = [[a[i][j] + lam[i]*cols[k][j] - lam[j]*cols[k][i] for j in range(n)] for i in range(n)]
            check(bpf(ap, cols) == bpf(a, cols), f"8.8(i) n={n} s={s}")
        # control: the wrong sign in (ii) must fail when the bordered term is non-zero
        q = bpf(a, cols + [E, O])
        if q != 0:
            check(bpf(aM, cols) != bpf(a, cols) + q, f"8.8 control n={n} s={s}")

# Corollary 8.9 (a), (b): random integer y (no box), symbolic ζ
def W(sg, y, r): return [[omega(2*sg+1, y[i], y[j], r) for j in range(len(y))] for i in range(len(y))]
for h in (1, 2):
    r = 2*h+1
    for n in range(1, 6):
        for s in range(0, n+1):
            for _ in range(2):
                y = [random.randint(-3, 3) for _ in range(n)]
                cols = [rc(n) for _ in range(s)]
                aN = [[Dm(y[i], y[j], r) for j in range(n)] for i in range(n)]
                H = [[sp.expand(sum(z**t * omega(2*(h+t)+1, y[i], y[j], r) for t in range(h))) for j in range(n)] for i in range(n)]
                Evc = [sum(z**al * yy**(2*al) for al in range(h+1)) for yy in y]
                Odc = [sum(z**be * yy**(2*be+1) for be in range(h)) for yy in y]
                if (n - s) % 2 == 0 and n >= s + 2:
                    t = (n - s)//2 - 1
                    lhs = bpf(aN, cols)
                    if t <= h-1:
                        rhs = (-1)**(t+1) * sp.Poly(bpf(H, cols + [Evc, Odc]), z).coeff_monomial(z**(h-1-t))
                    else:
                        rhs = 0
                    check(sp.expand(lhs - rhs) == 0, f"8.9(a) h={h} n={n} s={s}")
                if (n - s) % 2 == 1:
                    t = (n - s - 1)//2
                    lhs = bpf(aN, cols + [[yy**(r-1) for yy in y]])
                    if t <= h:
                        rhs = (-1)**t * sp.Poly(bpf(H, cols + [Evc]), z).coeff_monomial(z**(h-t))
                    else:
                        rhs = 0
                    check(sp.expand(lhs - rhs) == 0, f"8.9(b) h={h} n={n} s={s}")

# Lemma 8.7′ membership, linear algebra modulo a prime in the degree of the target
PR = 10007
def poly_vec(f, ys, r):
    """dict monomial-exponent-tuple -> coeff mod PR, in the box y^r = 0."""
    P = sp.Poly(sp.expand(f), *ys); out = {}
    for e, c in P.terms():
        if all(x < r for x in e):
            out[e] = (out.get(e, 0) + int(c)) % PR
    return {k: v for k, v in out.items() if v}

def rank_mod(rows):
    rows = [dict(r) for r in rows if r]; piv = {}
    rk = 0
    for r in rows:
        r = dict(r)
        while r:
            lead = max(r)
            if lead in piv:
                pr = piv[lead]; f = r[lead]
                for k, v in pr.items():
                    r[k] = (r.get(k, 0) - f*v) % PR
                    if r[k] == 0: del r[k]
            else:
                inv = pow(r[lead], PR-2, PR); r = {k: v*inv % PR for k, v in r.items()}
                piv[lead] = r; rk += 1; break
    return rk

def homog_parts(vec):
    out = {}
    for e, c in vec.items(): out.setdefault(sum(e), {})[e] = c
    return out

_MC = {}
def MONS(n, r, d):
    key = (n, r, d)
    if key not in _MC:
        _MC[key] = [m for m in itertools.product(range(r), repeat=n) if sum(m) == d]
    return _MC[key]

def in_ideal(target, gens, ys, r):
    """target in the ideal generated by gens in Z/PR[y]/(y^r)? Test degree by degree
    with the multiples of the generators by monomials."""
    tv = poly_vec(target, ys, r)
    if not tv: return True
    n = len(ys); parts = homog_parts(tv)
    gvecs = [poly_vec(g, ys, r) for g in gens]
    for d, tpart in parts.items():
        rows = []
        for gv in gvecs:
            for gd, gp in homog_parts(gv).items():
                md = d - gd
                if md < 0: continue
                for mon in MONS(n, r, md):
                    row = {}
                    for e, c in gp.items():
                        ee = tuple(a+b for a, b in zip(e, mon))
                        if all(x < r for x in ee): row[ee] = (row.get(ee, 0) + c) % PR
                    row = {k: v for k, v in row.items() if v}
                    if row: rows.append(row)
        r0 = rank_mod(rows); r1 = rank_mod(rows + [tpart])
        if r1 != r0: return False
    return True

def Ugens(ys, p, r):
    """generators Δ(S)·D_Q with |S| = p and Q a perfect matching of the rest."""
    n = len(ys); gens = []
    for S in itertools.combinations(range(n), p):
        rest = [i for i in range(n) if i not in S]
        if len(rest) % 2: continue
        V = 1
        for i, j in itertools.combinations(S, 2): V *= (ys[j] - ys[i])
        for m in matchings(rest):
            g = V
            for (a, b) in m: g *= D(ys[a], ys[b], r)
            gens.append(g)
    return gens

def Pf_N(ys, r, cols):
    n = len(ys)
    aN = [[Dm(ys[i], ys[j], r) for j in range(n)] for i in range(n)]
    return bpf(aN, cols)

cells = [(3,3,[]), (3,4,[0]), (3,5,[]), (5,3,[]), (5,4,[0]), (5,4,[1]), (5,5,[0,1]), (7,3,[]), (7,4,[2]),
         (3,4,[]), (5,4,[]), (7,4,[]), (3,5,[1]), (5,5,[0]), (5,5,[4]), (3,6,[]), (5,6,[0,1]), (3,6,[0,2])]
cells += [(7,5,[0]), (7,5,[2]), (7,5,[5]), (9,4,[]), (9,5,[3]), (7,4,[0,1]), (9,3,[])]
CNT = {'a': 0, 'b': 0, 'a_nonzero': 0, 'b_nonzero': 0}
for (r, n, es) in cells:
    ys = sp.symbols(f'y0:{n}')
    s = len(es)
    cols = [[yy**e for yy in ys] for e in es]
    if (n - s) % 2 == 0:   # case (a)
        P = Pf_N(ys, r, cols); ok = in_ideal(P, Ugens(ys, s+2, r), ys, r)
        check(ok, f"8.7′(a) r={r} n={n} e={es}"); CNT['a'] += 1; CNT['a_nonzero'] += (poly_vec(P, ys, r) != {})
    else:                   # case (b)
        P = Pf_N(ys, r, cols + [[yy**(r-1) for yy in ys]]); ok = in_ideal(P, Ugens(ys, s+1, r), ys, r)
        check(ok, f"8.7′(b) r={r} n={n} e={es}"); CNT['b'] += 1; CNT['b_nonzero'] += (poly_vec(P, ys, r) != {})

# Remark (3): r = 5, n = 3, border y^2 in place of y^{r-1}: NOT in 𝔘_0 (|S| = 1)
ys = sp.symbols('y0:3'); P = Pf_N(ys, 5, [[yy**2 for yy in ys]])
check(not in_ideal(P, Ugens(ys, 1, 5), ys, 5), "Remark (3): border y^2 at r=5 should fail")
check(poly_vec(P, ys, 5) != {}, "Remark (3): the Pfaffian is non-zero in the box")

# Remark (2): zero patterns. r=3 (h=1): l>=1, t>=1 ; l=0, t=2
# v12 after the cold reading (4 Oct): for l >= 1 the zero rule is l + t >= h + 1 (Remark (2)).
for (r, l, t) in [(3,1,1), (3,2,1), (3,0,2), (5,1,2), (5,0,3), (5,2,1), (7,2,2), (7,3,1)]:
    n = l + 1 + 2*t; ys = sp.symbols(f'y0:{n}')
    El = [r-1] if l == 0 else list(range(0, l-1))
    P = Pf_N(ys, r, [[yy**e for yy in ys] for e in El])
    check(sp.expand(P) == 0, f"Remark (2) zero: r={r} l={l} t={t}")
for (r, l, t) in [(5,1,1), (5,0,2), (3,0,1), (7,2,1)]:   # controls: below the threshold, non-zero
    n = l + 1 + 2*t; ys = sp.symbols(f'y0:{n}')
    El = [r-1] if l == 0 else list(range(0, l-1))
    P = Pf_N(ys, r, [[yy**e for yy in ys] for e in El])
    check(poly_vec(P, ys, r) != {}, f"Remark (2) control non-zero: r={r} l={l} t={t}")

# §1.3: gcd(m,(n+1)!) = 1  <=>  gcd(m,(n+2)!) = 1, k >= 1
for k in range(1, 12):
    n = 2*k
    for m in range(3, 400):
        check((math.gcd(m, math.factorial(n+1)) == 1) == (math.gcd(m, math.factorial(n+2)) == 1), f"(n+1)! k={k} m={m}")
# (8.1), (8.2), (8.4) and (F5) at r = 3, 5, 7
for r in (3, 5, 7):
    check(sp.expand(D(A_, B_, r) - D(B_, A_, r)) == 0, f"(8.1a) r={r}")
    check(sp.expand(Dm(A_, B_, r) + Dm(B_, A_, r)) == 0, f"(8.1b) r={r}")
    check(sp.expand(D(A_, B_, r) - (B_**(r-1) - A_*Dm(A_, B_, r))) == 0, f"(8.2) r={r}")
    check(sp.expand((A_+B_)*D(A_, B_, r) - (A_**r + B_**r)) == 0, f"(8.3a) r={r}")
    check(sp.expand((A_+B_)*Dm(A_, B_, r) - (B_**(r-1) - A_**(r-1))) == 0, f"(8.3b) r={r}")
    for u in range(r):
        check(sp.Poly(D(A_, B_, r), A_).coeff_monomial(A_**(r-1-u)) == (-1)**u * B_**u, f"(8.4a) r={r} u={u}")
    for u in range(r-1):
        check(sp.Poly(Dm(A_, B_, r), A_).coeff_monomial(A_**(r-2-u)) == -(-1)**u * B_**u, f"(8.4b) r={r} u={u}")
    yx = sp.Symbol('yx'); Np = sp.symbols('w0:2')
    aNp = [[Dm(Np[i], Np[j], r) for j in range(2)] for i in range(2)]
    for E in ([0], [1], [r-1]):
        cE = [[w**e for w in Np] for e in E]
        lhs = bpf(aNp, cE + [[Dm(yx, w, r) for w in Np]])
        rhs = -sum((-1)**u * yx**(r-2-u) * bpf(aNp, cE + [[w**u for w in Np]]) for u in range(r-1))
        check(sp.expand(lhs - rhs) == 0, f"(F5a) r={r} E={E}")
        lhs = bpf(aNp, cE + [[D(yx, w, r) for w in Np]])
        rhs = sum((-1)**u * yx**(r-1-u) * bpf(aNp, cE + [[w**u for w in Np]]) for u in range(r))
        check(sp.expand(lhs - rhs) == 0, f"(F5b) r={r} E={E}")

print("8.7' cells:", CNT)
check(CNT['a_nonzero'] >= 4 and CNT['b_nonzero'] >= 4, "enough non-zero memberships")
print(f"{CHECKS} checks, {FAILS} failures")
print("FIN-OK" if FAILS == 0 else "FIN-FAIL")
