"""
refuteW_mixed_lines.py -- adversarial re-check of the finding on Corollary W(i), paper line 748.

Question: along a path in the family  f_0(z_0,z_1)+...+f_d(z_{2d},z_{2d+1}) = 0, do the 'mixed'
standard subspaces L_{J,beta} (J in J(s,d) with a non-identity matching J' on {0..2s+1}) deform?

(A) Lines on S = { f_0(z_0,z_1) + f_1(z_2,z_3) = 0 } (d = 1).
    A line disjoint from l_1 = {z_2=z_3=0} is {(lam(a,b), a, b)} with lam in M_2(C), and it lies on S
    iff f_0(lam(a,b)) + f_1(a,b) == 0, i.e. f_1 = -f_0 o lam (lam singular forces f_1 = c*(linear)^m,
    impossible for squarefree f_1).  Lines meeting both l_0 and l_1 are the m^2 coordinate lines.
    So non-coordinate lines exist  iff  f_1 in GL_2 . f_0.
    - m = 3: every squarefree binary cubic is GL_2-equivalent to x^3+y^3 -> 18 extra lines (27 total):
      the referee's counterexample as literally stated ("no mixed line on a generic member") FAILS at m=3.
    - m = 5: f_0 = x^5+y^5; f_1 in GL_2.f_0 forces f_1 = -(l_1^5 + l_2^5), Waring rank <= 2, hence the
      3x4 catalecticant of f_1 has rank <= 2.  A generic quintic has catalecticant rank 3 -> no extra line.
      So along a path in the WHOLE family that perturbs f_0 generically, the 50 mixed Fermat lines do not
      persist: the counterexample is right for m >= 5 (paths leaving the subfamily f_0 = x^m+y^m).
(B) Subfamily f_0 = ... = f_s = x^m+y^m fixed, f_i (i>s) moving: the mixed subspace
    span(s-space of X(2s), P^{(s+1)}_nu(t), ..., P^{(d)}_nu(t)) lies in W_t identically.  Checked for
    s=1, d=2, m=5, J' = {{0,2},{1,3}} with a symbolic f_2 whose root (alpha:gamma) is symbolic.
"""
import sys, time, random, itertools
import sympy as sp

t0 = time.time()
random.seed(20260925)
a, b, p, q, r, s = sp.symbols('a b p q r s')

def count_solutions(polys, gens):
    """Number of standard monomials of a zero-dimensional ideal (solutions with multiplicity)."""
    G = sp.groebner(polys, *gens, order='grevlex')
    if list(G.exprs) == [1] or G.exprs == [sp.Integer(1)]:
        return 0, G
    lms = [sp.Poly(g, *gens).monoms(order='grevlex')[0] for g in G.exprs]
    # check zero-dimensional: each variable has a pure power among leading monomials
    for i in range(len(gens)):
        if not any(all(e[j] == 0 for j in range(len(gens)) if j != i) and e[i] > 0 for e in lms):
            return None, G
    bound = max(max(e) for e in lms) + 1
    cnt = 0
    for mono in itertools.product(range(bound), repeat=len(gens)):
        if not any(all(mono[j] >= e[j] for j in range(len(gens))) for e in lms):
            cnt += 1
    return cnt, G

def squarefree(f, x, y):
    fx = f.subs(y, 1)
    return sp.discriminant(sp.Poly(fx, x)) != 0

def extra_lines_equations(m, f1):
    # f_0 = x^m + y^m ; lambda = [[p,q],[r,s]] ; condition (pa+qb)^m + (ra+sb)^m + f1(a,b) == 0
    expr = sp.expand((p*a + q*b)**m + (r*a + s*b)**m + f1)
    P = sp.Poly(expr, a, b)
    return [c for c in P.coeffs()]

# ---------- (A) m = 3 ----------
m = 3
while True:
    coeffs = [random.randint(-3, 3) for _ in range(4)]
    f1 = coeffs[0]*a**3 + coeffs[1]*a**2*b + coeffs[2]*a*b**2 + coeffs[3]*b**3
    if coeffs[0] != 0 and coeffs[3] != 0 and squarefree(f1, a, b):
        break
eqs = extra_lines_equations(3, f1)
n3, G3 = count_solutions(eqs, [p, q, r, s])
print(f"[A m=3] f_0 = a^3+b^3, f_1 = {sp.factor(f1)} (squarefree, random)")
print(f"        equations f_1 = -f_0 o lambda : {len(eqs)} eqs in 4 unknowns; #solutions lambda = {n3}")
print(f"        lines: {m*m} coordinate + {n3} non-coordinate = {m*m + (n3 or 0)}   (expected 27 for any smooth cubic surface)")
# also the Fermat-Fermat cubic: f_1 = a^3 + b^3 -> also 18 (stabiliser of x^3+y^3 in GL_2 has order 18)
n3F, _ = count_solutions(extra_lines_equations(3, a**3 + b**3), [p, q, r, s])
print(f"        Fermat cubic surface (f_1 = a^3+b^3): non-coordinate lines = {n3F}, total = {9 + (n3F or 0)} (expected 27 = 3*m^2)")

# ---------- (A) m = 5 : catalecticant test ----------
def catalecticant(f, m):
    P = sp.Poly(f, a, b)
    # f = sum_i binom(m,i) c_i a^{m-i} b^i ; catalecticant rows k=0..2, cols j=0..m-2 : c_{k+j}
    c = []
    for i in range(m + 1):
        coeff = P.coeff_monomial(a**(m - i) * b**i)
        c.append(sp.Rational(coeff, sp.binomial(m, i)))
    rows = 3 if m == 5 else 2
    cols = m + 1 - rows + 1
    return sp.Matrix(rows, cols, lambda k, j: c[k + j])

m = 5
while True:
    coeffs = [random.randint(-3, 3) for _ in range(6)]
    f1 = sum(coeffs[i]*a**(5 - i)*b**i for i in range(6))
    if coeffs[0] != 0 and coeffs[5] != 0 and squarefree(f1, a, b):
        break
C = catalecticant(f1, 5)
rk = C.rank()
print(f"[A m=5] f_0 = a^5+b^5, f_1 = {f1} (squarefree, random)")
print(f"        3x4 catalecticant rank of f_1 = {rk}  (rank 3 => f_1 is not l_1^5 + l_2^5 => f_1 not in GL_2.(x^5+y^5) => NO non-coordinate line)")
Cf = catalecticant(a**5 + b**5, 5)
print(f"        control: catalecticant rank of a^5+b^5 = {Cf.rank()} (=2, consistent with 50 extra lines on the Fermat quintic surface)")
Cc = catalecticant(a**5 + 3*b**5, 5)
print(f"        control: catalecticant rank of a^5+3b^5 = {Cc.rank()} (=2: x^5+3y^5 IS in the orbit of x^5+y^5, so mixed lines persist there)")
print(f"        conclusion: for m=5 a generic perturbation of f_0 kills the mixed lines; for m=3 it does not (27 lines always).")

# ---------- (B) subfamily with f_0 = f_1 = x^m+y^m fixed, f_2 moving (s=1, d=2, m=5) ----------
m = 5
z = sp.symbols('z0:6')
beta, betap, alpha, gamma, w, u, v = sp.symbols('beta betap alpha gamma w u v')
c0, c1, c2, c3, c4, c5 = sp.symbols('c0:6')
f2 = sum(sp.Symbol(f'c{i}')*u**(5 - i)*v**i for i in range(6))   # generic binary quintic in (u,v)
# J' = {{0,2},{1,3}}: L: z2 = beta z0, z3 = betap z1 (beta^5 = betap^5 = -1); z4 = alpha w, z5 = gamma w
W = z[0]**5 + z[1]**5 + z[2]**5 + z[3]**5 + f2.subs({u: z[4], v: z[5]})
subsL = {z[2]: beta*z[0], z[3]: betap*z[1], z[4]: alpha*w, z[5]: gamma*w}
res = sp.expand(W.subs(subsL))
res = res.subs({beta**5: -1, betap**5: -1})
res = sp.expand(res)
# remaining term must be w^5 * f2(alpha, gamma), which vanishes when (alpha:gamma) is a root of f_2
rem = sp.simplify(res - w**5 * f2.subs({u: alpha, v: gamma}))
print(f"[B] s=1,d=2,m=5, J'={{{{0,2}},{{1,3}}}}: W|_L - w^5 f_2(alpha,gamma) = {rem}  (0 => L(t) subset W_t whenever (alpha:gamma) is a root of f_2(t))")

# ---------- (B') smooth <=> every f_i squarefree, d=1, m=5, random f_i (Euler) ----------
f0r = a**5 + b**5
Wd1 = f0r.subs({a: z[0], b: z[1]}) + f1.subs({a: z[2], b: z[3]})
grad = [sp.diff(Wd1, zi) for zi in z[:4]]
Gs = sp.groebner(grad + [Wd1], *z[:4], order='grevlex')
# singular locus in P^3 is empty iff the ideal of partials is (z0..z3)-primary; test: some power of each z_i in ideal
sat = all(any(sp.Poly(g, *z[:4]).monoms()[0] == tuple(5 if j == i else 0 for j in range(4)) or
               sp.reduced(zi**k, list(Gs.exprs), *z[:4], order='grevlex')[1] == 0
               for k in range(1, 12) for g in Gs.exprs) for i, zi in enumerate(z[:4]))
print(f"[B'] d=1, m=5, f_0 = a^5+b^5, f_1 random squarefree: ideal of partials is irrelevant (smooth) = {sat}")

print(f"done in {time.time()-t0:.1f}s")
