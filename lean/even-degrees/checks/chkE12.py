# chkE12.py — brute force for Lean piece E12 (q_oddbox_lifts_1.md): the lifts of the odd box,
# first part (paper v11, §8.6, Proposition 8.10: cases (A), (M, delta=0), (Z, delta=0), (R ordinary)).
# Grepy Mandalay, 3 Oct 2026.
# The Pfaffians are computed in the CONVENTION OF THE LEAN PROJECT (bmat, pf along the index 0),
# as in chkE11.py; the ring, the graded linear algebra, the slices W_j, the shapes and the
# interlaced pairs come from the auditor's engine of the cold audit (fria_engine.py).
# The memberships (T1)-(T5) are tested on the STATEMENTS: the slices are computed by linear
# algebra from the generators of V_Lambda; the constructions of the proofs are not used.
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
# ================= Part P: the marked Pfaffian with one new variable =================
for r in (3, 5, 7):
    h = (r - 1) // 2
    for l in range(1, h + 2):
        if l + 1 > 5: continue
        R = Box(l + 1, r, P0); S2 = Box(l, r, P0)
        P = mPf(R, h, l, list(range(l + 1)))            # index 0 is X, indices 1..l are w_0..w_{l-1}
        vd = S2.vdm(list(range(l))); sg = (-1) ** (l * (l + 1) // 2)
        for k in range(r):
            if k > 2 * h - l and k > l - 2:
                check("P1 r=%d l=%d k=%d" % (r, l, k), not P[k].any())
        if l <= h:
            check("P2 r=%d l=%d" % (r, l), not ((P[2 * h - l] - sg * vd) % P0).any())
            for k in range(2 * h - l + 1, r):
                check("P3 r=%d l=%d k=%d" % (r, l, k), not P[k].any())
            control("P2 with the opposite sign, r=%d l=%d" % (r, l), ((P[2 * h - l] + sg * vd) % P0).any())
        else:
            control("P2 at l = h + 1 (the formula should fail), r=%d l=%d" % (r, l), ((P[2 * h - l] - sg * vd) % P0).any())
    # (P0)
    R1 = Box(1, r, P0)
    check("P0 r=%d" % r, not ((mPf(R1, h, 0, [0]) - R1.var(0, 2 * h)) % P0).any())
print("Part P done: checks %d fail %d" % (NCHK, NFAIL)); sys.stdout.flush()

# ================= (L1): incl(markedPf_l(B)) = markedPf_l(B^+) =================
for (r, m) in ((3, 5), (5, 4), (7, 3)):
    h = (r - 1) // 2; R = Box(m, r, P0); S2 = Box(m - 1, r, P0)
    for l in range(0, h + 1):
        for sz in range(l + 1, m, 2):
            for B in itertools.combinations(range(m - 1), sz):
                g = mPf(S2, h, l, list(B)); emb = R.zero(); emb[0] = g
                check("L1 r=%d m=%d l=%d B=%s" % (r, m, l, B), not ((mPf(R, h, l, [b + 1 for b in B]) - emb) % P0).any())
print("L1 done: checks %d fail %d" % (NCHK, NFAIL)); sys.stdout.flush()

# ================= Part T, (I): single shapes Lambda = {(lam, delta)} =================
cnt = {"T1": 0, "T2": 0, "T3": 0, "T4": 0, "T5": 0}
cnz = {"T1": 0, "T2": 0, "T3": 0, "T4": 0, "T5": 0}      # the memberships of NON-ZERO products
dpos = {"T1": 0, "T2": 0, "T3": 0, "T4": 0, "T5": 0}     # non-zero products tested in a slice d >= 1
def memb(S2, W, d, G):                                   # W is None when V_Lambda = 0: then W_d = 0
    if W is None: return not G.any()
    return S2.member(W[d], G)
low = {"T1": [0, 0], "T2": [0, 0], "T3": [0, 0], "T4": [0, 0], "T5": [0, 0]}   # [cases with d >= 1, cases where some product is outside W_{d-1}]
def test_slice(tag, S2, W, d, prods, name):
    if not prods: return
    for G in prods:
        check("%s %s" % (tag, name), memb(S2, W, d, G))
        cnt[tag] += 1
        if G.any():
            cnz[tag] += 1
            if d >= 1: dpos[tag] += 1
    if d >= 1 and any(G.any() for G in prods):
        low[tag][0] += 1
        if any(not memb(S2, W, d - 1, G) for G in prods): low[tag][1] += 1
for (r, m, p) in ((3, 2, 101), (3, 3, 101), (3, 4, 101), (3, 5, 101), (3, 6, 101), (3, 4, 2), (3, 5, 3),
                  (5, 2, 101), (5, 3, 101), (5, 4, 101), (5, 5, 101), (5, 4, 2), (5, 5, 2), (5, 4, 5),
                  (7, 2, 101), (7, 3, 101), (7, 4, 101), (7, 3, 7)):
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); idx2 = list(range(m - 1))
    for lam in all_partitions_upto(m):
        for e in (0, 1):
            if (m - sum(lam) - e) % 2 or sum(lam) + e > m: continue
            gens = gens_VS(R, h, [(lam, e)], idx)
            if gens: S2, W = R.slices(R.ideal(gens))
            else: S2, W = Box(m - 1, r, p), None        # V_Lambda = 0: every slice is 0
            cl = columns(lam)
            # insertion: lam has the columns of mu except that the column cs is one longer
            for cs in range(1, len(cl) + 1):
                if cl[cs - 1] > (cl[cs] if cs < len(cl) else 0):
                    mc = cl[:]; mc[cs - 1] -= 1; mu = from_cols(mc); d = colLen(mu, cs)
                    if d > 2 * h: continue
                    if e == 0:
                        test_slice("T1", S2, W, d, products_of(S2, h, mu, 0, idx2), "r=%d m=%d p=%d lam=%s mu=%s cs=%d" % (r, m, p, lam, mu, cs))
                    elif cs >= 2:
                        test_slice("T3", S2, W, d, products_of(S2, h, mu, 1, idx2), "r=%d m=%d p=%d lam=%s mu=%s cs=%d" % (r, m, p, lam, mu, cs))
            # removal: lam has the columns of mu except that the column c0 is one shorter
            for c0 in range(1, len(cl) + 2):
                prev = cl[c0 - 2] if c0 >= 2 else None
                here = cl[c0 - 1] if c0 <= len(cl) else 0
                if c0 >= 2 and not (prev > here): continue
                mc = cl[:] + [0]; mc[c0 - 1] += 1; mu = from_cols(mc); k = colLen(mu, c0)
                if not (1 <= k <= 2 * h + 1): continue
                d = 2 * h + 1 - k
                if e == 0:
                    test_slice("T2", S2, W, d, products_of(S2, h, mu, 0, idx2), "r=%d m=%d p=%d lam=%s mu=%s c0=%d" % (r, m, p, lam, mu, c0))
                elif c0 >= 2:
                    test_slice("T4", S2, W, d, products_of(S2, h, mu, 1, idx2), "r=%d m=%d p=%d lam=%s mu=%s c0=%d" % (r, m, p, lam, mu, c0))
            # the zero option of an unmarked shape: Lambda = {(mu, 1)}, tight patterns of mu
            if e == 1 and len(lam) <= h:
                test_slice("T5", S2, W, 2 * h - len(lam), products_of(S2, h, lam, 0, idx2), "r=%d m=%d p=%d mu=%s" % (r, m, p, lam))
    print("single shapes, cell r=%d m=%d p=%d: cumulative memberships %s, of non-zero products %s" % (r, m, p, cnt, cnz)); sys.stdout.flush()
for tag in ("T1", "T2", "T3", "T4", "T5"):
    control("(%s) single shapes: in the cases with d >= 1, some product lies outside the slice d - 1 (%d of %d cases)" % (tag, low[tag][1], low[tag][0]), low[tag][1] > 0)
# a control with a reason: (T5) needs l(mu) <= h. For l(mu) = h + 1 the slice 2h - l is not reached in general.
badT5 = 0; triedT5 = 0
for (r, m, p) in ((3, 3, 101), (3, 5, 101), (5, 4, 101), (5, 5, 101)):
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); idx2 = list(range(m - 1))
    for mu in all_partitions_upto(m - 1):
        if len(mu) != h + 1 or (m - 1 - sum(mu)) % 2: continue
        gens = gens_VS(R, h, [(mu, 1)], idx)
        if gens: S2, W = R.slices(R.ideal(gens))
        else: S2, W = Box(m - 1, r, p), None
        d = 2 * h - len(mu)
        prods = products_of(S2, h, mu, 0, idx2)
        if not prods or d < 0: continue
        triedT5 += 1
        if any(not memb(S2, W, d, G) for G in prods): badT5 += 1
control("(T5) at l(mu) = h + 1: some product outside the slice 2h - l (%d of %d cases)" % (badT5, triedT5), badT5 > 0)

# ================= Part T, (II): inside the interlaced pairs, the slice r - F_Lambda(sigma) =================
kinds = {}; kindsnz = {}; kindsd = {}; lowII = [0, 0]; e13 = {"M1": 0, "Z1": 0, "R1": 0}; e13bad = 0
for (r, m, p) in ((3, 2, 101), (3, 3, 101), (3, 4, 101), (3, 5, 101), (3, 6, 101), (3, 4, 2), (3, 5, 3),
                  (5, 2, 101), (5, 3, 101), (5, 4, 101), (5, 5, 101), (5, 5, 2), (5, 4, 5),
                  (7, 2, 101), (7, 3, 101), (7, 4, 101), (7, 3, 7)):
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); idx2 = list(range(m - 1))
    IP = interlaced_pairs(m, h); S1 = Sh(m - 1, h)
    for L in IP:
        gens = gens_VS(R, h, L, idx)
        S2, W = R.slices(R.ideal(gens))
        for (mu, e) in S1:
            Phi = F_formula(L, mu, e, h, r)
            if Phi < 1: continue
            l = len(mu); d = r - Phi; tag = None
            if Phi <= l:
                rho = Phi; c0 = mu[rho - 1]
                check("bookkeeping R: rho is the last row of its length", rho == l or mu[rho] < mu[rho - 1])
                if e == 0 or c0 >= 2:
                    tag = "R,delta=%d (T%d)" % (e, 2 if e == 0 else 4)
                    lam = minus(mu, rho - 1)
                    check("bookkeeping R ordinary", (lam, e) in L and colLen(mu, c0) == rho and d == 2 * h + 1 - colLen(mu, c0)
                          and all(colLen(lam, c) + (1 if c == c0 else 0) == colLen(mu, c) for c in range(1, m + 2)))
                else: tag = "R1"
            elif Phi == l + 1:
                if e == 0:
                    tag = "Z,delta=0 (T5)"
                    check("bookkeeping Z0", (mu, 1) in L and l <= h and d == 2 * h - l)
                else: tag = "Z1"
            elif Phi <= r - l:
                check("bookkeeping M: Phi = r - l", Phi == r - l)
                if e == 0:
                    tag = "M,delta=0 (T1)"
                    lam = tuple(mu) + (1,)
                    check("bookkeeping M0", (lam, 0) in L and d == l == colLen(mu, 1)
                          and all(colLen(lam, c) == colLen(mu, c) + (1 if c == 1 else 0) for c in range(1, m + 2)))
                else: tag = "M1"
            else:
                j0 = r - Phi + 1; lam = plus(mu, j0 - 1); cs = mu[j0 - 1] + 1
                tag = "A,delta=%d (T%d)" % (e, 1 if e == 0 else 3)
                check("bookkeeping A", (lam, e) in L and cs >= 2 and colLen(mu, cs) == j0 - 1 and d == j0 - 1 and d <= 2 * h
                      and all(colLen(lam, c) == colLen(mu, c) + (1 if c == cs else 0) for c in range(1, m + 2)))
            prods = products_of(S2, h, mu, e, idx2)
            if not prods: continue
            okall = True
            for G in prods:
                ok = S2.member(W[d], G); okall = okall and ok
                if tag in e13:
                    if not ok: e13bad += 1
                    if not ok: print("NOTE (E13 case %s, not part of this piece) outside the slice: r=%d m=%d p=%d L=%s sigma=%s" % (tag, r, m, p, sorted(L), (mu, e)))
                    e13[tag] += 1
                else:
                    check("II %s r=%d m=%d p=%d L=%s sigma=%s" % (tag, r, m, p, sorted(L), (mu, e)), ok)
                    kinds[tag] = kinds.get(tag, 0) + 1
                    if G.any():
                        kindsnz[tag] = kindsnz.get(tag, 0) + 1
                        if d >= 1: kindsd[tag] = kindsd.get(tag, 0) + 1
            if tag not in e13 and d >= 1:
                lowII[0] += 1
                if any(not S2.member(W[d - 1], G) for G in prods): lowII[1] += 1
    print("interlaced pairs, cell r=%d m=%d p=%d: %d pairs; cumulative %s; E13 cases seen (products) %s" % (r, m, p, len(IP), kinds, e13)); sys.stdout.flush()
control("(II) inside the interlaced pairs, one slice lower (r - Phi - 1): some product outside in %d of %d cases with d >= 1" % (lowII[1], lowII[0]), lowII[1] > 0)
print("memberships by lemma (single shapes):", cnt)
print("  of non-zero products:", cnz, "; of these in a slice d >= 1:", dpos)
print("memberships by case (interlaced pairs):", kinds)
print("  of non-zero products:", kindsnz, "; of these in a slice d >= 1:", kindsd)
print("E13 cases seen in advance (products):", e13, "; outside their slice:", e13bad)
print("TOTAL checks %d, failures %d; controls %d, fire %d" % (NCHK, NFAIL, NCTL, NFIRE))
print("FIN-OK" if NFAIL == 0 else "FIN-CON-FALLOS")
