# chkE13.py — brute force for Lean piece E13 (q_oddbox_lifts_2.md): the lifts of the odd box,
# second part (paper v11, §8.6, Proposition 8.10: cases (Z, delta=1), (M, delta=1), (R, delta=1, mu_rho = 1)).
# Grepy Mandalay, 3 Oct 2026. Started from chkE12.py (helpers copied unchanged).
# Part Q: Lemma Q and Lemma Q' as polynomial identities in R[X], tested by evaluation of w at random
# points of F_p (no truncation), in the convention of the Lean project.
# Part T: the lifts (T6)-(T8) tested on the STATEMENTS, with the slices computed by linear algebra
# from the generators of V_Lambda (auditor's engine fria_engine.py), (I) for the smallest sets of
# shapes allowed by the hypotheses, (II) inside every interlaced pair, with the case read off the chain.
import sys, itertools, random
sys.path.insert(0, '/Users/rafa/Desktop/ARBOLYAML/corpus4/regla298_sky')
import numpy as np
from fria_engine import *
random.seed(20261003)
NCHK = 0; NFAIL = 0; NCTL = 0; NFIRE = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1; print("FAIL", name); sys.stdout.flush()
def control(name, fires):
    global NCTL, NFIRE
    NCTL += 1
    if fires: NFIRE += 1
    print("control", name, "FIRES" if fires else "SILENT"); sys.stdout.flush()

# ---- the Lean convention (as in chkE11.py) ----
def lean_pf(R, A):
    m = len(A)
    if m == 0: return R.one()
    if m % 2: return R.zero()
    tot = R.zero()
    for jp in range(m - 1):
        e = A[0][jp + 1]
        if e is None or not e.any(): continue
        idx = [i for i in range(m) if i not in (0, jp + 1)]
        sub = lean_pf(R, [[A[i][j] for j in idx] for i in idx])
        if sub.any(): tot = (tot + (-1) ** jp * R.mul(e, sub)) % R.p
    return tot
def lean_bmat(R, a, c):
    n = len(a); s = len(c); N = n + s
    B = [[None] * N for _ in range(N)]
    for i in range(n):
        for j in range(n): B[i][j] = a[i][j]
        for k in range(s):
            B[i][n + k] = c[k][i]; B[n + k][i] = (-c[k][i]) % R.p
    return B
def mPf(R, h, l, pts):
    n = len(pts)
    a = [[R.Bk(pts[i], pts[j]) if i != j else R.zero() for j in range(n)] for i in range(n)]
    exps = [2 * h] if l == 0 else list(range(l - 1))
    c = [[R.var(pts[i], e) for i in range(n)] for e in exps]
    return lean_pf(R, lean_bmat(R, a, c))
def marked_patterns(lam, idx):
    l = len(lam); cols = columns(lam); out = []
    for sz in range(l + 1, len(idx) + 1, 2):
        for B0 in itertools.combinations(idx, sz):
            rest0 = [x for x in idx if x not in B0]
            free = len(rest0) - sum(cols[1:])
            if free < 0 or free % 2: continue
            for P in kpairs(rest0, free // 2):
                used = {x for pr in P for x in pr}; rest = [x for x in rest0 if x not in used]
                for Bs in blocks(rest, cols[1:]):
                    out.append((P, B0, Bs))
    return out
def marked_product(R, h, lam, T):
    P, B0, Bs = T
    return R.prod([R.D(min(a, b), max(a, b)) for a, b in P] + [mPf(R, h, len(lam), sorted(B0))] + [R.vdm(B) for B in Bs])
def gens_VS(R, h, L, idx):
    out = []
    for (lam, e) in L:
        if e == 0:
            out += pattern_products(R, (lam, 0), idx)
        else:
            for T in marked_patterns(lam, idx):
                g = marked_product(R, h, lam, T)
                if g.any(): out.append(g)
    return out
def products_of(S2, h, mu, e, idx2):
    if e == 0: return pattern_products(S2, (mu, 0), idx2)
    return [marked_product(S2, h, mu, T) for T in marked_patterns(mu, idx2)]
def colLen(lam, c):
    return sum(1 for x in lam if x >= c)
def from_cols(cols):
    cols = [c for c in cols if c > 0]
    return tuple(sum(1 for c in cols if c >= i) for i in range(1, (cols[0] if cols else 0) + 1))
def all_partitions_upto(n):
    return [lam for s in range(0, n + 1) for lam in partitions(s, s)]

P0 = 32003

# ---- polynomials in X over F_P (for Part Q) ----
PQ = 32003
def pmul(a, b): return np.convolve(a, b) % PQ
def padd(a, b):
    n = max(len(a), len(b)); c = np.zeros(n, dtype=np.int64); c[:len(a)] += a; c[:len(b)] += b
    return c % PQ
def pscal(s, a): return (s * np.asarray(a)) % PQ
def const(v): return np.array([v % PQ], dtype=np.int64)
X = np.array([0, 1], dtype=np.int64)
def ppow(a, e):
    out = const(1)
    for _ in range(e): out = pmul(out, a)
    return out
def iszero(a): return not (np.asarray(a) % PQ).any()
def coeff(a, k): return int(a[k]) % PQ if k < len(a) else 0
def Dm(r, a, b):
    tot = const(0)
    for u in range(r - 1): tot = padd(tot, pscal((-1) ** u, pmul(ppow(a, u), ppow(b, r - 2 - u))))
    return tot
def Dp(r, a, b):
    tot = const(0)
    for u in range(r): tot = padd(tot, pscal((-1) ** u, pmul(ppow(a, u), ppow(b, r - 1 - u))))
    return tot
def qpf(A):
    m = len(A)
    if m == 0: return const(1)
    if m % 2: return const(0)
    tot = const(0)
    for jp in range(m - 1):
        e = A[0][jp + 1]
        if iszero(e): continue
        idx = [i for i in range(m) if i not in (0, jp + 1)]
        sub = qpf([[A[i][j] for j in idx] for i in idx])
        if not iszero(sub): tot = padd(tot, pscal((-1) ** jp, pmul(e, sub)))
    return tot
def qPf(r, ys, cols):
    n = len(ys); s = len(cols); N = n + s
    B = [[const(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            if i != j: B[i][j] = Dm(r, ys[i], ys[j])
        for k in range(s):
            B[i][n + k] = cols[k][i]; B[n + k][i] = pscal(-1, cols[k][i])
    return qpf(B)
def qE(h, l): return [2 * h] if l == 0 else list(range(l - 1))
def qmPf(h, l, ys): return qPf(2 * h + 1, ys, [[ppow(y, e) for y in ys] for e in qE(h, l)])

# ================= Part Q =================
ctlQ = [0, 0]; ctlQp = [0, 0]
for h in (0, 1, 2, 3, 4):
    r = 2 * h + 1
    for trial in range(3):
        # Lemma Q: z = (X, w), |w| = l + 2 + 2t; (Q1) for l <= h, (Q2) for l + 1 <= h, sign (-1)^l
        for l in range(0, h + 1):
            for t in range(0, 3):
                n = l + 2 + 2 * t
                if n > 7: continue
                w = [const(random.randrange(PQ)) for _ in range(n)]
                Pz = qmPf(h, l, [X] + w); top = qmPf(h, l + 1, w)
                for k in range(2 * h - l + 1, max(len(Pz), 2 * h - l + 2)):
                    check("Q1 h=%d l=%d t=%d k=%d" % (h, l, t, k), coeff(Pz, k) == 0)
                if l + 1 <= h:
                    check("Q2 h=%d l=%d t=%d" % (h, l, t), (coeff(Pz, 2 * h - l) - (-1) ** l * coeff(top, 0)) % PQ == 0)
                    if coeff(top, 0):
                        ctlQ[0] += 1
                        if (coeff(Pz, 2 * h - l) + (-1) ** l * coeff(top, 0)) % PQ: ctlQ[1] += 1
        # Lemma Q': |w| = ell + 1 + 2t, F = X * mPf_{ell+1}(X, w) + Pf(w; y^{E_{ell+1}}, D(X, .)); every ell <= h + 1
        for ell in range(0, h + 2):
            L = ell + 1
            for t in range(0, 3):
                n = ell + 1 + 2 * t
                if n > 7: continue
                w = [const(random.randrange(PQ)) for _ in range(n)]
                cols = [[ppow(y, e) for y in w] for e in qE(h, L)] + [[Dp(r, X, y) for y in w]]
                Pf2 = qPf(r, w, cols); Xm = pmul(X, qmPf(h, L, [X] + w))
                Fq = padd(Xm, Pf2); top = qmPf(h, ell, w)
                for k in range(ell + 1, max(len(Fq), ell + 2)):
                    check("Q'1 h=%d ell=%d t=%d k=%d" % (h, ell, t, k), coeff(Fq, k) == 0)
                check("Q'2 h=%d ell=%d t=%d" % (h, ell, t), (coeff(Fq, ell) - coeff(top, 0)) % PQ == 0)
                Fbad = padd(Xm, pscal(-1, Pf2))
                if any(coeff(Xm, k) for k in range(ell + 1, len(Xm))):
                    ctlQp[0] += 1
                    if any(coeff(Fbad, k) for k in range(ell + 1, len(Fbad))): ctlQp[1] += 1
control("(Q2) with the opposite sign: wrong in %d of %d cases with a non-zero top" % (ctlQ[1], ctlQ[0]), ctlQ[1] > 0)
control("(Q'1) with the minus sign: degree > ell in %d of %d cases where X*mPf has degree > ell" % (ctlQp[1], ctlQp[0]), ctlQp[1] > 0)
print("Part Q done: checks %d fail %d" % (NCHK, NFAIL)); sys.stdout.flush()

# ================= Part T =================
def memb(S2, W, d, G):
    if W is None: return not G.any()
    return S2.member(W[d], G)
cnt = {"T6": 0, "T7": 0, "T8": 0}; cnz = {"T6": 0, "T7": 0, "T8": 0}; low = {"T6": [0, 0], "T7": [0, 0], "T8": [0, 0]}
def test_slice(tag, S2, W, d, prods, name):
    if not prods: return
    for G in prods:
        check("%s %s" % (tag, name), memb(S2, W, d, G)); cnt[tag] += 1
        if G.any(): cnz[tag] += 1
    if d >= 1 and any(G.any() for G in prods):
        low[tag][0] += 1
        if any(not memb(S2, W, d - 1, G) for G in prods): low[tag][1] += 1
def slicesof(R, h, L, idx, r, m, p):
    gens = gens_VS(R, h, L, idx)
    if gens: return R.slices(R.ideal(gens))
    return Box(m - 1, r, p), None
CELLS = ((3, 2, 101), (3, 3, 101), (3, 4, 101), (3, 5, 101), (3, 6, 101), (3, 4, 2), (3, 5, 3),
         (5, 2, 101), (5, 3, 101), (5, 4, 101), (5, 5, 101), (5, 4, 2), (5, 5, 2), (5, 4, 5),
         (7, 2, 101), (7, 3, 101), (7, 4, 101), (7, 3, 7))
noM0 = [0, 0]; T7eqh = [0, 0]
for (r, m, p) in CELLS:
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); idx2 = list(range(m - 1))
    for mu in all_partitions_upto(m - 1):
        if (m - sum(mu)) % 2: continue              # marked patterns of mu on m - 1 indices: |mu| + 1 = m - 1 mod 2
        l = len(mu)
        prods = products_of(Box(m - 1, r, p), h, mu, 1, idx2)
        if not prods: continue
        name = "r=%d m=%d p=%d mu=%s" % (r, m, p, mu)
        # (T6) (Z, delta = 1): Lambda = {(mu, 0)}, l <= h, 1 <= h, slice 2h - l
        if l <= h and h >= 1:
            S2, W = slicesof(R, h, [(mu, 0)], idx, r, m, p)
            test_slice("T6", S2, W, 2 * h - l, products_of(S2, h, mu, 1, idx2), name)
        # (T7) (M, delta = 1): Lambda = {(mu + one row 1, 1), (mu, 0)}, l < h, slice l
        lam1 = tuple(mu) + (1,)
        if l < h:
            S2, W = slicesof(R, h, [(lam1, 1), (mu, 0)], idx, r, m, p)
            test_slice("T7", S2, W, l, products_of(S2, h, mu, 1, idx2), name)
            # control with a reason: without (mu, 0) the patterns with t = 0 are not reached
            S2b, Wb = slicesof(R, h, [(lam1, 1)], idx, r, m, p)
            pr = [G for G in products_of(S2b, h, mu, 1, idx2) if G.any()]
            if pr:
                noM0[0] += 1
                if any(not memb(S2b, Wb, l, G) for G in pr): noM0[1] += 1
        elif l == h and h >= 1:
            S2, W = slicesof(R, h, [(lam1, 1), (mu, 0)], idx, r, m, p)
            pr = [G for G in products_of(S2, h, mu, 1, idx2) if G.any()]
            if pr:
                T7eqh[0] += 1
                if any(not memb(S2, W, l, G) for G in pr): T7eqh[1] += 1
        # (T8) (R, delta = 1, mu_l = 1): Lambda = {(mu - e_l, 1)}, 1 <= l <= h, slice 2h + 1 - l
        if 1 <= l <= h and mu[-1] == 1:
            S2, W = slicesof(R, h, [(minus(mu, l - 1), 1)], idx, r, m, p)
            test_slice("T8", S2, W, 2 * h + 1 - l, products_of(S2, h, mu, 1, idx2), name)
    print("single shapes, cell r=%d m=%d p=%d: cumulative %s, non-zero %s" % (r, m, p, cnt, cnz)); sys.stdout.flush()
for tag in ("T6", "T7", "T8"):
    control("(%s) one slice lower: some product outside in %d of %d cases with d >= 1" % (tag, low[tag][1], low[tag][0]), low[tag][1] > 0)
control("(T7) without (mu, 0) in Lambda: some product outside the slice in %d of %d cases" % (noM0[1], noM0[0]), noM0[1] > 0)
print("NOTE (T7) at l(mu) = h (outside the statement): product outside the slice in %d of %d cases" % (T7eqh[1], T7eqh[0]))

# ---- (II) inside the interlaced pairs ----
kinds = {"M1": 0, "Z1": 0, "R1": 0}; kindsnz = {"M1": 0, "Z1": 0, "R1": 0}
for (r, m, p) in CELLS:
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); idx2 = list(range(m - 1))
    IP = interlaced_pairs(m, h); S1 = Sh(m - 1, h)
    for L in IP:
        S2, W = R.slices(R.ideal(gens_VS(R, h, L, idx)))
        for (mu, e) in S1:
            if e != 1: continue
            Phi = F_formula(L, mu, e, h, r)
            if Phi < 1: continue
            l = len(mu); d = r - Phi; tag = None
            if Phi <= l:
                rho = Phi
                if mu[rho - 1] == 1:
                    tag = "R1"
                    check("bookkeeping R1 (T8 hypotheses)", rho == l and (minus(mu, l - 1), 1) in L and 1 <= l <= h and d == 2 * h + 1 - l)
            elif Phi == l + 1:
                tag = "Z1"
                check("bookkeeping Z1 (T6 hypotheses)", (mu, 0) in L and l <= h and h >= 1 and d == 2 * h - l)
            elif Phi <= r - l:
                tag = "M1"
                check("bookkeeping M1 (T7 hypotheses)", (tuple(mu) + (1,), 1) in L and (mu, 0) in L and l < h and d == l)
            if tag is None: continue
            for G in products_of(S2, h, mu, 1, idx2):
                check("II %s r=%d m=%d p=%d L=%s sigma=%s" % (tag, r, m, p, sorted(L), (mu, e)), S2.member(W[d], G))
                kinds[tag] += 1
                if G.any(): kindsnz[tag] += 1
    print("interlaced pairs, cell r=%d m=%d p=%d: %d pairs; cumulative %s, non-zero %s" % (r, m, p, len(IP), kinds, kindsnz)); sys.stdout.flush()
print("memberships by lemma (single shapes):", cnt, "; non-zero:", cnz)
print("memberships by case (interlaced pairs):", kinds, "; non-zero:", kindsnz)
print("TOTAL checks %d, failures %d; controls %d, fire %d" % (NCHK, NFAIL, NCTL, NFIRE))
print("FIN-OK" if NFAIL == 0 else "FIN-CON-FALLOS")
