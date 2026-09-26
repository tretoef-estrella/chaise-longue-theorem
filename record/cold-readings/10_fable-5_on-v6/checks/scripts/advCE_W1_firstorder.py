"""
advCE_W1_firstorder.py -- adversarial verifier (lens COUNTEREXAMPLE) for the finding on
Corollary W(i), paper line 748 / [DS, Sec. 4.6, source lines 1822-1831].

Question. Along a path in the WHOLE family  W = { sum_i f_i(z_{2i}, z_{2i+1}) = 0 }, do the mixed
standard d-spaces L_{J,beta}, J in J(s,d) with a non-identity matching J' on {0..2s+1}, deform to
linear subspaces of the intermediate fibres?  The finding says: only if the path keeps
f_0 = ... = f_s = x^m + y^m.

Instance (smallest one where a deformation is actually needed, i.e. d > s):
  s = 1, d = 2, X : z_0^m + ... + z_5^m = 0 in P^5, m odd.
  Mixed plane   Pi_mix  = { z_2 = -z_0, z_3 = -z_1, z_5 = -z_4 }   (J = [[0,2],[1,3],[4,5]])
  Product plane Pi_prod = { z_1 = -z_0, z_3 = -z_2, z_5 = -z_4 }   (J = J_0 = [[0,1],[2,3],[4,5]])
  Both lie on X because m is odd.

Test 1 (exact, over Q).  First-order deformation of the plane in the direction G_t = G + t*h.
  Planes near Pi are z_dep = z_dep(Pi) + sum_j a_{dep,j} u_j (u = the 3 free coordinates), 9 unknowns.
  Linearising G_t|_Pi(a) = 0 at (a,t) = (0,0):   sum_{dep,j} a_{dep,j} * (dG/dz_dep)|_Pi * u_j + t*h|_Pi = 0
  as a form of degree m in u.  A first-order deformation of Pi in the direction h exists iff h|_Pi lies in
  the column span of the 9 vectors (dG/dz_dep)|_Pi * u_j.  (If it does not, no analytic family
  Pi_t subset W_t with Pi_0 = Pi exists along any analytic path with tangent h at X.)
  We test h = every monomial of f_0-type (in z_0,z_1), f_1-type (z_2,z_3), f_2-type (z_4,z_5),
  and a random integer form of each type, for m = 3, 5, 7, for both planes.
  We also compute the tangent space at x^m+y^m of the GL_2-orbit of x^m+y^m, namely
  span{x^{m-1}, y^{m-1}} * span{x, y}, and compare it with the set of unobstructed f_0-directions.

Test 2 (numeric, numpy).  Lines on the surface S = { f_0(z_0,z_1) + f_1(z_2,z_3) = 0 }, d = 1.
  Every line on S is a product line (m^2 of them) or the graph of A in GL_2 with f_1 o A = -f_0
  (a line meeting {z_0=z_1=0} or {z_2=z_3=0} is a product line when the f_i are squarefree).
  A exists iff a Moebius map sends the root set of f_0 onto the root set of f_1, and then there are
  exactly m matrices A over that map (scalars lambda with lambda^m c = -1).  We count the Moebius maps by
  checking all bijections of the root sets against a 3-point normalisation (cross-ratio test).
  Cases: f_0 = x^m+y^m; f_1 = x^m+y^m (Fermat), f_1 = random squarefree, f_1 = x^m + 3 y^m (in the orbit).

Prediction: < 5 s, < 80 MB.
"""
import sys, time, random, itertools
import numpy as np
import sympy as sp

t0 = time.time()
random.seed(20260925)

# ----------------------------------------------------------------------------------------------
# Test 1: first-order deformations of the two planes, m = 3, 5, 7
# ----------------------------------------------------------------------------------------------
z = sp.symbols('z0:6')

def first_order_solvable(m, plane, h):
    """plane: dict dep_index -> (free_index, sign) meaning z_dep = sign * z_free on Pi.
       Returns True iff h|_Pi lies in the span of (dG/dz_dep)|_Pi * u_j."""
    free = [i for i in range(6) if i not in plane]
    u = [z[i] for i in free]
    subs = {z[dep]: sgn * z[fr] for dep, (fr, sgn) in plane.items()}
    G = sum(zi**m for zi in z)
    cols = []
    for dep in plane:
        dG = sp.diff(G, z[dep]).subs(subs)
        for uj in u:
            cols.append(sp.expand(dG * uj))
    target = sp.expand(h.subs(subs))
    # coordinates w.r.t. all monomials of degree m in u
    monos = [sp.Mul(*[u[k]**e[k] for k in range(3)])
             for e in itertools.product(range(m + 1), repeat=3) if sum(e) == m]
    def vec(expr):
        P = sp.Poly(expr, *u)
        d = dict(zip(P.monoms(), P.coeffs()))
        return [d.get(tuple(sp.Poly(mo, *u).monoms()[0]), 0) for mo in monos]
    M = sp.Matrix([vec(c) for c in cols]).T          # (#monos) x 9
    b = sp.Matrix(vec(target))
    rM = M.rank()
    rMb = M.row_join(b).rank()
    return rM == rMb, rM

Pi_mix = {2: (0, -1), 3: (1, -1), 5: (4, -1)}
Pi_prod = {1: (0, -1), 3: (2, -1), 5: (4, -1)}

x, y = sp.symbols('x y')
print("=" * 78)
print("TEST 1: first-order deformations of a mixed plane vs a product plane on the Fermat 4-fold")
print("        (s=1, d=2; direction h added to the equation; 'ok' = deforms to first order)")
print("=" * 78)
for m in (3, 5, 7):
    # sanity: both planes lie on X
    G = sum(zi**m for zi in z)
    for name, plane in (("Pi_mix", Pi_mix), ("Pi_prod", Pi_prod)):
        subs = {z[dep]: sgn * z[fr] for dep, (fr, sgn) in plane.items()}
        assert sp.expand(G.subs(subs)) == 0, (m, name)
    # tangent space of the GL_2-orbit of x^m+y^m at x^m+y^m
    orbit_T = [sp.expand(x**(m - 1) * x), sp.expand(x**(m - 1) * y), sp.expand(y**(m - 1) * x), sp.expand(y**(m - 1) * y)]
    orbit_monos = set()
    for e in orbit_T:
        orbit_monos |= set(sp.Poly(e, x, y).monoms())
    print(f"\n--- m = {m} ---")
    print(f"  tangent space of GL_2-orbit of x^m+y^m: monomials x^i y^j with (i,j) in {sorted(orbit_monos)}"
          f"  (dim {len(orbit_monos)} of {m+1})")
    for name, plane in (("Pi_mix ", Pi_mix), ("Pi_prod", Pi_prod)):
        results = {}
        for blk, (i0, i1) in (("f0", (0, 1)), ("f1", (2, 3)), ("f2", (4, 5))):
            row = []
            for k in range(m + 1):
                h = z[i0]**(m - k) * z[i1]**k
                ok, r = first_order_solvable(m, plane, h)
                row.append(ok)
            # random integer form of this block
            hr = sum(random.randint(-5, 5) * z[i0]**(m - k) * z[i1]**k for k in range(m + 1))
            okr, r = first_order_solvable(m, plane, hr)
            results[blk] = (row, okr, r)
        for blk in ("f0", "f1", "f2"):
            row, okr, r = results[blk]
            mono_str = " ".join(("ok " if v else "OBS") for v in row)
            print(f"  {name}  h in block {blk}: monomials k=0..{m} [x^(m-k) y^k]: {mono_str} | random form: "
                  f"{'ok' if okr else 'OBSTRUCTED'}   (rank of linearisation = {r})")
        # compare unobstructed f0-monomials with orbit tangent space
        row = results["f0"][0]
        unobs = {(m - k, k) for k, v in enumerate(row) if v}
        if name.strip() == "Pi_mix":
            print(f"  {name}  unobstructed f0-monomials = {sorted(unobs)} ; equals orbit tangent monomials: "
                  f"{unobs == orbit_monos}")
        else:
            print(f"  {name}  unobstructed f0-monomials = all {len(unobs)} of {m+1}: {len(unobs) == m + 1}")

# ----------------------------------------------------------------------------------------------
# Test 2: lines on f_0(z_0,z_1) + f_1(z_2,z_3) = 0 via Moebius maps between root sets (numeric)
# ----------------------------------------------------------------------------------------------
print("\n" + "=" * 78)
print("TEST 2: lines on S = { x^m+y^m (z0,z1) + f_1(z2,z3) = 0 }, counted as m^2 product lines")
print("        + m * #(Moebius maps roots(f_0) -> roots(f_1)) graph lines")
print("=" * 78)

def roots_of_form(coeffs):
    """coeffs of f(x,1) in decreasing degree; returns roots as complex numbers (affine chart y=1)."""
    r = np.roots(coeffs)
    return r

def moebius_from_3(p, q):
    """Moebius map sending p[0],p[1],p[2] -> q[0],q[1],q[2]; returns 2x2 matrix."""
    # map p -> (0, 1, inf) then inverse of q -> (0,1,inf)
    def to_std(a):
        a0, a1, a2 = a
        return np.array([[a1 - a2, -a0 * (a1 - a2)], [a1 - a0, -a2 * (a1 - a0)]], dtype=complex)
    A = np.linalg.inv(to_std(q)) @ to_std(p)
    return A

def count_moebius(r0, r1, tol=1e-7):
    m = len(r0)
    cnt = 0
    for perm in itertools.permutations(range(m)):
        q = [r1[perm[i]] for i in range(3)]
        A = moebius_from_3(r0[:3], q)
        good = True
        for i in range(3, m):
            v = A @ np.array([r0[i], 1.0])
            if abs(v[1]) < 1e-12:
                good = False
                break
            img = v[0] / v[1]
            if abs(img - r1[perm[i]]) > tol * max(1.0, abs(img)):
                good = False
                break
        if good:
            cnt += 1
    return cnt

for m in (3, 5, 7):
    fermat = [1] + [0] * (m - 1) + [1]           # x^m + y^m in chart y=1: x^m + 1
    r_fermat = roots_of_form(fermat)
    cases = {
        "f_1 = x^m+y^m (Fermat)": fermat,
        "f_1 = x^m + 3 y^m (in GL_2-orbit of Fermat)": [1] + [0] * (m - 1) + [3],
    }
    while True:
        c = [random.randint(-4, 4) for _ in range(m + 1)]
        c[0] = c[0] if c[0] != 0 else 1
        P = sp.Poly(sum(c[i] * x**(m - i) for i in range(m + 1)), x)
        if sp.discriminant(P) != 0 and P.degree() == m:
            break
    cases[f"f_1 = random squarefree {list(c)}"] = c
    print(f"\n--- m = {m}: f_0 = x^m + y^m ---")
    for label, coeffs in cases.items():
        r1 = roots_of_form(coeffs)
        nM = count_moebius(list(r_fermat), list(r1))
        graph = m * nM
        total = m * m + graph
        print(f"  {label:48s}: #Moebius = {nM:3d}, graph lines = {graph:4d}, total lines = {total:4d}"
              f"   (3*m^2 = {3*m*m})")

print(f"\ndone in {time.time() - t0:.2f}s")
