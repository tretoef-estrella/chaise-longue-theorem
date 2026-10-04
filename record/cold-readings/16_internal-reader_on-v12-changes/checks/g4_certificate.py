# G4 — M5 over Z: the proof of Lemma 8.7' run as a certificate.
# For each cell: expand Pf(H; c, Ev, Od) (resp. Pf(H; c, Ev)) by (F7); divide each border determinant det_S by
# Delta(S) EXACTLY in Z[zeta][y] (the Vandermonde divisibility); expand Pf(H|_{N\S}) with H_ij = D(y_i,y_j)Od(y_j);
# take the coefficient of zeta of Corollary 8.9 with its sign; compare with Pf(N; c) from the definition, in Z[y]/(y^r).
import sys, itertools, random
sys.path.insert(0, 'checks')
from pflib import matchings, perm_sign, pf_def
import sympy as sp

zeta = sp.Symbol('zeta')
rng = random.Random(99)

def box_reduce(expr, ys, r):
    P = sp.Poly(sp.expand(expr), *ys, zeta)
    d = {}
    for mon, co in P.terms():
        if all(e < r for e in mon[:len(ys)]):
            d[mon] = d.get(mon, 0) + co
    return sp.Poly.from_dict(d, *ys, zeta) if d else sp.Poly(0, *ys, zeta)

def run_cell(r, n, s, E, case, ctrl_log):
    h = (r-1)//2
    ys = sp.symbols(f'y0:{n}')
    T = sp.Symbol('T')
    Ev = sum(zeta**al * T**(2*al) for al in range(h+1))
    Od = sum(zeta**be * T**(2*be+1) for be in range(h))
    borders = [T**e for e in E] + ([Ev, Od] if case == 'a' else [Ev])
    sp_ = len(borders)
    Dp = lambda u, v: sum((-1)**k * u**k * v**(r-1-k) for k in range(r))
    Dm = lambda u, v: sum((-1)**k * u**k * v**(r-2-k) for k in range(r-1))
    OdF = lambda u: Od.subs(T, u)
    N = list(range(n))
    full = 0; terms = []; nondiv = 0
    for S in itertools.combinations(N, sp_):
        M = sp.Matrix([[b.subs(T, ys[i]) for b in borders] for i in S])
        detS = sp.expand(M.det(method='berkowitz'))
        DeltaS = sp.prod([ys[S[j]] - ys[S[i]] for i in range(len(S)) for j in range(i+1, len(S))])
        q = sp.cancel(detS / DeltaS)
        num, den = sp.fraction(sp.together(q))
        ok_div = (den == 1) and sp.Poly(sp.expand(q), *ys, zeta).domain == sp.ZZ
        if not ok_div: nondiv += 1
        sgnS = (-1)**(sum(S) - sp_*(sp_-1)//2)
        rest = [i for i in N if i not in S]
        pfH = 0
        for Q in matchings(rest):
            sg = perm_sign([v for pr in Q for v in pr])
            term = sg
            for (i, j) in Q:
                term = term * Dp(ys[i], ys[j]) * OdF(ys[j])
            pfH += term
        tS = sgnS * DeltaS * sp.expand(q) * pfH
        terms.append(tS)
        full += tS
    full = (-1)**(sp_*(sp_-1)//2) * full
    fullP = box_reduce(full, ys, r)
    if case == 'a':
        t = (n - s)//2 - 1; j = h-1-t; sign = (-1)**(t+1); jbad = h-t
    else:
        t = (n - s - 1)//2; j = h-t; sign = (-1)**t; jbad = h-t+1
    def zcoef(P, k):
        if k < 0: return sp.Integer(0)
        return sp.expand(sum(co * sp.prod([v**e for v, e in zip(ys, mon[:n])]) for mon, co in P.terms() if mon[n] == k))
    cert = sp.expand(sign * zcoef(fullP, j))
    # left side: Pf(N; c) from the definition, c = y^E (and y^{r-1} in case b), reduced to the box
    cols = [[ys[i]**e for i in N] for e in E] + ([] if case == 'a' else [[ys[i]**(r-1) for i in N]])
    k = n; ss = len(cols)
    Mx = [[0]*(k+ss) for _ in range(k+ss)]
    for a_ in range(k):
        for b_ in range(k):
            if a_ != b_: Mx[a_][b_] = Dm(ys[a_], ys[b_])
    for c_ in range(ss):
        for a_ in range(k):
            Mx[a_][k+c_] = cols[c_][a_]; Mx[k+c_][a_] = -cols[c_][a_]
    lhs = pf_def(Mx, len(Mx), sp.Integer(1), sp.Integer(0))
    lhsP = box_reduce(lhs, ys, r)
    lhs_e = sp.expand(lhsP.as_expr())
    ok = sp.expand(lhs_e - cert) == 0
    nonzero = lhs_e != 0
    # controls (only meaningful when the left side is non-zero)
    c1 = c2 = None
    if nonzero:
        bad = sp.expand(sign * zcoef(fullP, jbad))
        c1 = sp.expand(lhs_e - bad) != 0
        if len(terms) > 1:
            fullP2 = box_reduce((-1)**(sp_*(sp_-1)//2) * (full*(-1)**(sp_*(sp_-1)//2) - terms[0]), ys, r)
            c2 = sp.expand(lhs_e - sign * zcoef(fullP2, j)) != 0
    ctrl_log.append((c1, c2))
    return ok, nonzero, nondiv

cells = []
for r in (3, 5, 7):
    for n in range(2, 6 if r < 7 else 5):
        for s in range(0, 3):
            if n - s >= 2 and (n - s) % 2 == 0:
                cells.append((r, n, s, tuple(range(s)), 'a'))           # Lemma 8.7 borders E_{s+1}
                if s >= 1:
                    cells.append((r, n, s, tuple(sorted(rng.sample(range(r), s))), 'a'))
            if n - s >= 1 and (n - s) % 2 == 1 and s <= 1:
                cells.append((r, n, s, tuple(sorted(rng.sample(range(r-1), s))), 'b'))
ok_all = 0; nz = 0; nd = 0; ctrl = []
for (r, n, s, E, case) in cells:
    ok, nonzero, nondiv = run_cell(r, n, s, E, case, ctrl)
    ok_all += ok; nz += nonzero; nd += nondiv
    print(f'r={r} n={n} s={s} E={E} case={case}: identity {"OK" if ok else "FAIL"}; Pf non-zero: {nonzero}; non-divisible dets: {nondiv}; controls {ctrl[-1]}', flush=True)
print(f'\ncells {len(cells)}; identity holds in {ok_all}; non-zero left side in {nz}; non-exact Vandermonde divisions: {nd}')
c1 = [c for c, _ in ctrl if c is not None]; c2 = [c for _, c in ctrl if c is not None]
print(f'control 1 (wrong power of zeta) fired {sum(c1)}/{len(c1)}; control 2 (one S dropped) fired {sum(c2)}/{len(c2)}')
