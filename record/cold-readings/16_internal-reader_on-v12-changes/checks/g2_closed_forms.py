# G2 — M1 (omega_s, (8.6)), M3 (homogeneity, top coefficients), M4 (Corollary 8.9), M5 (H = D*Od in the box;
# certificate of Lemma 8.7' over Z with exact Vandermonde division over Z[zeta][y]).
import sys, random, itertools
sys.path.insert(0, 'checks')
from pflib import *
import sympy as sp
from flint import fmpz_poly

rng = random.Random(4102026)
res = {}
def rec(name, ok, tot, cf, extra=''):
    res[name] = (ok, tot, cf)
    print(f'{name}: {ok}/{tot} hold; control fired {cf} {extra}', flush=True)

a, b, z = sp.symbols('a b zeta')

def omega(s, r, A, B):
    return sum((-1)**u * A**u * B**(s-u) for u in range(0, r) if 0 <= s-u <= r-1)

def reduce_box(expr, vars_, r):
    P = sp.Poly(sp.expand(expr), *vars_)
    out = 0
    for mon, co in P.terms():
        if all(e < r for e in mon[:len(vars_)]):
            out += co * sp.prod([v**e for v, e in zip(vars_, mon)])
    return sp.expand(out)

# ---------- M1 ----------
ok = tot = cf = 0
for r in (3, 5, 7, 9, 11):
    h = (r-1)//2
    for s in range(1, 2*r-2, 2):
        w = omega(s, r, a, b)
        tot += 2; ok += (sp.expand(omega(s, r, b, a) + w) == 0) + (sp.expand(w.subs(b, a)) == 0)
    tot += 1; ok += (sp.expand(omega(r-2, r, a, b) - Dm(a, b, r)) == 0)
    for i in range(1, r-1, 2):
        lhs = omega(r-1+i, r, a, b); rhs = reduce_box(b**i * Dp(a, b, r), [a, b], r)
        bad = reduce_box(a**i * Dp(a, b, r), [a, b], r)
        tot += 1; ok += (sp.expand(lhs - rhs) == 0); cf += (sp.expand(lhs - bad) != 0)
    Ev = lambda X: sum(z**al * X**(2*al) for al in range(h+1))
    Od = lambda X: sum(z**be * X**(2*be+1) for be in range(h))
    L = sum(z**sg * omega(2*sg+1, r, a, b) for sg in range(2*h))
    tot += 1; ok += (sp.expand(L - (Ev(a)*Od(b) - Ev(b)*Od(a))) == 0)
    cf += (sp.expand(L - (Ev(b)*Od(a) - Ev(a)*Od(b))) != 0)
rec('M1 omega_s antisymmetry, omega_{r-2}=D^-, second item, (8.6)  [r=3..11]', ok, tot, cf)

# ---------- helpers over Z[zeta] with integer y ----------
def fp(coeffs):
    return fmpz_poly(coeffs)
ZERO = fmpz_poly([]); ONE = fmpz_poly([1])
def omega_int(s, r, x, y):
    return sum((-1)**u * x**u * y**(s-u) for u in range(0, r) if 0 <= s-u <= r-1)

def Hmat(ys, r):
    h = (r-1)//2; n = len(ys)
    M = [[ZERO]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                M[i][j] = fmpz_poly([omega_int(2*(h+tau)+1, r, ys[i], ys[j]) for tau in range(h)])
    return M
def Ev_col(ys, r):
    h = (r-1)//2
    return [fmpz_poly([y**(2*al) for al in range(h+1)]) for y in ys]
def Od_col(ys, r):
    h = (r-1)//2
    return [fmpz_poly([y**(2*be+1) for be in range(h)]) for y in ys]
def coef(p, k):
    return int(p[k]) if 0 <= k <= p.degree() else 0
def bordered_poly(a, cols):
    n = len(a); s = len(cols)
    M = [[ZERO]*(n+s) for _ in range(n+s)]
    for i in range(n):
        for j in range(n):
            M[i][j] = a[i][j]
    for k in range(s):
        for i in range(n):
            M[i][n+k] = cols[k][i]; M[n+k][i] = -cols[k][i]
    return M
def pf_poly(a, cols):
    M = bordered_poly(a, cols)
    return pf_def(M, len(M), ONE, ZERO)

# ---------- M3 ----------
ok = tot = cf = 0
for n in range(0, 7):
    for s in range(0, 4):
        if (n - s) < 0 or (n - s) % 2: continue
        kap = (n - s)//2
        for _ in range(4):
            aa = rand_alt(n, rng=rng); cc = [[rng.randint(-4, 4) for _ in range(n)] for _ in range(s)]
            tau = rng.randint(-3, 3)
            tot += 1; ok += (pf_b([[tau*x for x in row] for row in aa], cc) == tau**kap * pf_b(aa, cc))
            d = rng.randint(0, 2); dk = [rng.randint(0, 2) for _ in range(s)]
            A = [[ZERO]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    v = fmpz_poly([rng.randint(-3, 3) for _ in range(d+1)]); A[i][j] = v; A[j][i] = -v
            C = [[fmpz_poly([rng.randint(-3, 3) for _ in range(dk[k]+1)]) for _ in range(n)] for k in range(s)]
            P = pf_poly(A, C); top = kap*d + sum(dk)
            Atop = [[coef(A[i][j], d) for j in range(n)] for i in range(n)]
            Ctop = [[coef(C[k][i], dk[k]) for i in range(n)] for k in range(s)]
            T = pf_b(Atop, Ctop)
            tot += 2; ok += (P.degree() <= top) + (coef(P, top) == T)
            if T != 0 and top >= 1:
                cf += (coef(P, top-1) != T)
rec('M3 homogeneity and top coefficients', ok, tot, cf)

# ---------- M4: Corollary 8.9 over Z[zeta], integer y, random integer borders ----------
okA = totA = cfA = nzA = 0; okB = totB = cfB = nzB = 0; zeroA = zeroB = 0
for r in (3, 5, 7):
    h = (r-1)//2
    for n in range(1, 8):
        for s in range(0, 4):
            for _ in range(3):
                ys = [rng.randint(-4, 4) for _ in range(n)]
                aN = [[Dm(ys[i], ys[j], r) if i != j else 0 for j in range(n)] for i in range(n)]
                H = Hmat(ys, r); Ev = Ev_col(ys, r); Od = Od_col(ys, r)
                cc = [[rng.randint(-3, 3) for _ in range(n)] for _ in range(s)]
                ccp = [[fmpz_poly([v]) for v in col] for col in cc]
                if n - s >= 2 and (n - s) % 2 == 0 and n + s <= 9:   # (a)
                    t = (n - s)//2 - 1
                    L = pf_b(aN, cc)
                    if t <= h-1:
                        R = pf_poly(H, ccp + [Ev, Od])
                        val = (-1)**(t+1) * coef(R, h-1-t)
                        totA += 1; okA += (L == val); nzA += (L != 0)
                        cfA += (L != (-1)**(t+1) * coef(R, h-t)) if L != 0 else 0
                    else:
                        totA += 1; okA += (L == 0); zeroA += 1
                if n - s >= 1 and (n - s) % 2 == 1 and n + s + 1 <= 9:   # (b)
                    t = (n - s - 1)//2
                    L = pf_b(aN, cc + [[y**(r-1) for y in ys]])
                    if t <= h:
                        R = pf_poly(H, ccp + [Ev])
                        val = (-1)**t * coef(R, h-t)
                        totB += 1; okB += (L == val); nzB += (L != 0)
                        cfB += (L != (-1)**(t+1) * coef(R, h-t)) if L != 0 else 0
                    else:
                        totB += 1; okB += (L == 0); zeroB += 1
rec('M4 Corollary 8.9(a)', okA, totA, cfA, f'(non-zero LHS: {nzA}; cases t>=h checked =0: {zeroA})')
rec('M4 Corollary 8.9(b)', okB, totB, cfB, f'(non-zero LHS: {nzB}; cases t>h checked =0: {zeroB})')

# ---------- M5 (1): H_ij = D(y_i,y_j)*Od(y_j) in Z[y_i,y_j]/(y^r)[zeta] ----------
ok = tot = cf = 0
for r in (3, 5, 7, 9):
    h = (r-1)//2
    Hij = sum(z**tau * omega(2*(h+tau)+1, r, a, b) for tau in range(h))
    Odb = sum(z**be * b**(2*be+1) for be in range(h)); Oda = sum(z**be * a**(2*be+1) for be in range(h))
    good = reduce_box(Dp(a, b, r)*Odb, [a, b], r); bad = reduce_box(Dp(a, b, r)*Oda, [a, b], r)
    tot += 1; ok += (sp.expand(reduce_box(Hij, [a, b], r) - good) == 0); cf += (sp.expand(reduce_box(Hij, [a, b], r) - bad) != 0)
rec('M5 H_ij = D(y_i,y_j) Od(y_j) in the box', ok, tot, cf)

print('\nSUMMARY')
allok = True
for k, (o, t, c) in res.items():
    if o != t: allok = False
    print(f"  {'OK' if o == t else 'FAIL'}  {k}: {o}/{t}; control fired {c}")
print('ALL HOLD:', allok)
