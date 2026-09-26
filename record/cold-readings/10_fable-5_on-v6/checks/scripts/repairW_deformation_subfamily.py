# Adversarial-verifier check (lens REPAIR) for the finding on Cor. W(i), paper line 748 / [DS, 4.6].
# Three cheap symbolic facts, m = 5 (odd), sympy only.
#  (a) W = sum f_i(z_{2i}, z_{2i+1}) = 0 is singular iff some f_i has a multiple root (Euler).
#  (b) On the subfamily U_s (f_0 = ... = f_s = x^m + y^m, f_i squarefree for i > s) the span of a
#      standard s-space of X(2s) and root points P^{(i)}_nu of f_i (i > s) lies in W  -> mixed
#      d-spaces deform along ANY path in U_s.
#  (c) If f_0 is perturbed away from x^m + y^m, no line z_2 = b z_0, z_3 = b' z_1 lies on
#      f_0(z_0,z_1) + f_1(z_2,z_3) = 0  (the finding's s = d = 1 illustration, diagonal form).
import sympy as sp, random, time
t0 = time.time()
m = 5
x, y = sp.symbols('x y')
z = sp.symbols('z0:6')

# (a) smoothness criterion: random squarefree f_i -> gradient system has only the zero solution;
#     f_2 with a double root -> explicit singular point.
random.seed(1)
def rand_form():
    return sum(random.randint(-3, 3) * x**(m-i) * y**i for i in range(m+1)) + x**m + 7*y**m
f = [rand_form() for _ in range(3)]
assert all(sp.discriminant(fi.subs(y, 1), x) != 0 for fi in f)
F = sum(fi.subs({x: z[2*i], y: z[2*i+1]}) for i, fi in enumerate(f))
grad = [sp.diff(F, zi) for zi in z]
# Euler check: z . grad = m F
assert sp.expand(sum(z[i]*grad[i] for i in range(6)) - m*F) == 0
# squarefree f_i => grad f_i vanishes only at (0,0): resultant of the two partials is nonzero
for fi in f:
    gx, gy = sp.diff(fi, x), sp.diff(fi, y)
    assert sp.resultant(gx.subs(y, 1), gy.subs(y, 1), x) != 0
print("(a) all f_i squarefree => no common zero of the partials except 0 => W smooth : OK")
f2_double = sp.expand((x - y)**2 * (x**3 + 2*y**3))          # double root at (1:1)
F_sing = f[0].subs({x: z[0], y: z[1]}) + f[1].subs({x: z[2], y: z[3]}) + f2_double.subs({x: z[4], y: z[5]})
P = {z[0]: 0, z[1]: 0, z[2]: 0, z[3]: 0, z[4]: 1, z[5]: 1}
assert F_sing.subs(P) == 0 and all(sp.diff(F_sing, zi).subs(P) == 0 for zi in z)
print("(a') f_2 with a double root => (0:0:0:0:1:1) is a singular point of W : OK")

# (b) s = 1, d = 2: f_0 = f_1 = x^5 + y^5, f_2 random squarefree.  Mixed line on X(2):
#     z_2 = b z_0, z_3 = b' z_1 with b^5 = b'^5 = -1 (J' = [[0,2],[1,3]]).  Plane = span(line, P^{(2)}_nu).
b, bp, lam, mu, rho = sp.symbols('b bp lam mu rho')
f2 = f[2]
roots2 = sp.Poly(f2.subs(y, 1), x).all_roots()          # roots (alpha : 1) of f_2, exact algebraic numbers
alpha = roots2[0]
W1 = (z[0]**m + z[1]**m) + (z[2]**m + z[3]**m) + f2.subs({x: z[4], y: z[5]})
# generic point of the plane: lam*(1,0,b,0,0,0) + mu*(0,1,0,bp,0,0) + rho*(0,0,0,0,alpha,1)
pt = {z[0]: lam, z[1]: mu, z[2]: b*lam, z[3]: bp*mu, z[4]: rho*alpha, z[5]: rho}
val = sp.expand(W1.subs(pt))
val = val.subs({b**m: -1, bp**m: -1})
val = sp.expand(val)
# remaining term: rho^m * f_2(alpha, 1), which is 0 since alpha is a root
val = sp.simplify(val.subs(rho, 1))
assert val == 0, val
print("(b) span(mixed line of X(2), root point of random squarefree f_2) lies in W in U_1 : OK")

# (c) s = d = 1 illustration: f_0 = x^5 + y^5 + eps*x^4*y (eps != 0), f_1 = x^5 + y^5.
#     Line z_2 = b z_0, z_3 = b' z_1 lies on f_0 + f_1 = 0  iff  f_1(b x, b' y) = -f_0(x, y)
#     iff b^5 x^5 + b'^5 y^5 = -(x^5 + y^5 + eps x^4 y): the x^4 y coefficient forces eps = 0.
eps = sp.symbols('eps')
f0p = x**m + y**m + eps*x**4*y
cond = sp.Poly(sp.expand((b*x)**m + (bp*y)**m + f0p), x, y).coeffs()
sols = sp.solve(cond, [b, bp, eps], dict=True)
assert all(s.get(eps, None) == 0 for s in sols), sols
print("(c) no diagonal-form mixed line on f_0 + f_1 = 0 once f_0 is perturbed (eps != 0) : OK")
print("elapsed %.2fs" % (time.time() - t0))
