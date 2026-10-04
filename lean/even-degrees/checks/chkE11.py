# chkE11.py — brute force for Lean piece E11 (q_oddbox_patterns.md): the patterns of the odd box
# (Definition 8.6 of paper v11), the ideals V_Lambda, relabelling, and Lemma 8.7 in the ring C_m.
# Grepy Mandalay, 2 Oct 2026.
# The Pfaffians are computed in the CONVENTION OF THE LEAN PROJECT (bmat, pf along the index 0),
# written here from Pfaffian/Basic.lean and Pfaffian/Bordered.lean; the ring, the graded linear
# algebra, the shapes, the interlaced pairs and the count |Z_Lambda| come from the auditor's own
# engine of the cold audit (corpus4/regla298_sky/fria_engine.py), whose bordered Pfaffian pfE
# expands the paper's Pfaffian directly and is used here only as an independent comparison.
import sys, itertools, random
sys.path.insert(0, '/Users/rafa/Desktop/ARBOLYAML/corpus4/regla298_sky')
import numpy as np
from fria_engine import *
random.seed(20261002)
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

# ---- the Lean convention ----
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
    # mPf_l(z) with z_i = y_{pts[i]}: Pfe (2h+1) z E_l, E_0 = (2h), E_l = (0..l-2)
    n = len(pts)
    a = [[R.Bk(pts[i], pts[j]) if i != j else R.zero() for j in range(n)] for i in range(n)]
    exps = [2 * h] if l == 0 else list(range(l - 1))
    c = [[R.var(pts[i], e) for i in range(n)] for e in exps]
    return lean_pf(R, lean_bmat(R, a, c))
def eqpm(R, A, B):
    if not ((A - B) % R.p).any(): return 1
    if not ((A + B) % R.p).any(): return -1
    return 0
def sgn(perm):
    s = 1; perm = list(perm)
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]: s = -s
    return s

# ---- the patterns, generated from the conditions of the Lean structure (no count of pairs imposed) ----
def marked_patterns(lam, idx):
    l = len(lam); cols = columns(lam); out = []
    for sz in range(l + 1, len(idx) + 1, 2):
        for B0 in itertools.combinations(idx, sz):
            rest0 = [x for x in idx if x not in B0]
            free = len(rest0) - sum(cols[1:])        # what the blocks of the columns c >= 2 leave: it must be matched perfectly
            if free < 0 or free % 2: continue
            for P in kpairs(rest0, free // 2):
                used = {x for pr in P for x in pr}; rest = [x for x in rest0 if x not in used]
                for Bs in blocks(rest, cols[1:]):  # blocks() yields only if the blocks cover `rest` exactly
                    out.append((P, B0, Bs))
    return out
def marked_product(R, h, lam, T, pairfun=None):
    P, B0, Bs = T
    pf_ = pairfun or R.D
    return R.prod([pf_(min(a, b), max(a, b)) for a, b in P] + [mPf(R, h, len(lam), sorted(B0))] + [R.vdm(B) for B in Bs])
def gens_VS(R, h, L, idx, pairfun=None):
    out = []
    for (lam, e) in L:
        if e == 0:
            out += pattern_products(R, (lam, 0), idx)
        else:
            for T in marked_patterns(lam, idx):
                g = marked_product(R, h, lam, T, pairfun)
                if g.any(): out.append(g)
    return out
def relabel(R, g, sig):                 # y_i -> y_{sig[i]}
    inv = [0] * R.m
    for i, s_ in enumerate(sig): inv[s_] = i
    return np.transpose(g, inv)

P0 = 32003
# ================= Part A =================
for r in (3, 5, 7):
    h = (r - 1) // 2; R = Box(3, r, P0)
    Bk = R.Bk; v = R.var
    check("A1 r=%d" % r, not ((mPf(R, h, 0, [0]) - v(0, 2 * h)) % P0).any())
    check("A2 r=%d" % r, not ((mPf(R, h, 1, [0, 1]) - Bk(0, 1)) % P0).any())
    A3 = (R.mul(v(2, 2 * h), Bk(0, 1)) - R.mul(v(1, 2 * h), Bk(0, 2)) + R.mul(v(0, 2 * h), Bk(1, 2))) % P0
    check("A3 r=%d" % r, not ((mPf(R, h, 0, [0, 1, 2]) - A3) % P0).any())
    A3bad = (R.mul(v(2, 2 * h), Bk(0, 1)) + R.mul(v(1, 2 * h), Bk(0, 2)) + R.mul(v(0, 2 * h), Bk(1, 2))) % P0
    control("A3 with all signs plus, r=%d" % r, ((mPf(R, h, 0, [0, 1, 2]) - A3bad) % P0).any())
    A4 = (Bk(0, 1) - Bk(0, 2) + Bk(1, 2)) % P0
    check("A4 r=%d" % r, not ((mPf(R, h, 2, [0, 1, 2]) - A4) % P0).any())
    A4bad = (Bk(0, 1) + Bk(0, 2) + Bk(1, 2)) % P0
    control("A4 with all signs plus, r=%d" % r, ((mPf(R, h, 2, [0, 1, 2]) - A4bad) % P0).any())
    control("A2 with D in the place of D^-, r=%d" % r, ((mPf(R, h, 1, [0, 1]) - R.D(0, 1)) % P0).any())
for r in (3, 5):
    h = (r - 1) // 2; R = Box(4, r, P0)
    for n in range(1, 5):
        for l in range(0, 7):
            val = mPf(R, h, l, list(range(n)))
            if (n + l) % 2 == 0: check("A5 r=%d n=%d l=%d" % (r, n, l), not val.any())
            if l >= 1 and n + 1 < l: check("A6 r=%d n=%d l=%d" % (r, n, l), not val.any())
    control("A6 at n + 1 = l (n=2, l=3), r=%d" % r, mPf(R, h, 3, [0, 1]).any())
    control("A5 at n + l odd (n=3, l=0), r=%d" % r, mPf(R, h, 0, [0, 1, 2]).any())
    for n in range(1, 5):
        for l in range(0, 4):
            if (n + l) % 2 == 0: continue
            base = mPf(R, h, l, list(range(n)))
            for _ in range(6):
                sig = list(range(n)); random.shuffle(sig)
                check("A7 r=%d n=%d l=%d" % (r, n, l), not ((mPf(R, h, l, sig) - sgn(sig) * base) % P0).any())
            if n >= 2 and base.any():
                sig = [1, 0] + list(range(2, n))
                control("A7 without the sign (a transposition), r=%d n=%d l=%d" % (r, n, l), ((mPf(R, h, l, sig) - base) % P0).any())
print("Part A done: checks %d fail %d" % (NCHK, NFAIL)); sys.stdout.flush()

# ================= Lean convention against the engine of the cold audit =================
signs = {}
for (r, m) in ((3, 5), (5, 4), (7, 3)):
    h = (r - 1) // 2; R = Box(m, r, P0)
    for l in range(0, h + 1):
        for sz in range(l + 1, m + 1, 2):
            for B in itertools.combinations(range(m), sz):
                e = eqpm(R, mPf(R, h, l, list(B)), R.pfE(B, E_of(l, r)))
                check("engine r=%d m=%d l=%d B=%s" % (r, m, l, B), e != 0)
                signs.setdefault((l, sz), set()).add(e)
print("Lean convention vs engine, sign by (l, |B|):", {k: sorted(v) for k, v in sorted(signs.items())}); sys.stdout.flush()

# ================= Parts B, C, D and the count =================
tot_pairs = 0; tot_eq = 0
for (r, m, p) in ((3, 1, 101), (3, 2, 101), (3, 3, 101), (3, 4, 101), (3, 5, 101), (3, 3, 2), (3, 4, 2), (3, 5, 3),
                  (5, 1, 101), (5, 2, 101), (5, 3, 101), (5, 4, 101), (5, 3, 2), (5, 4, 5),
                  (7, 1, 101), (7, 2, 101), (7, 3, 101), (7, 3, 7)):
    h = (r - 1) // 2; R = Box(m, r, p); idx = list(range(m)); S = Sh(m, h)
    # (B3) on every marked pattern
    for (lam, e) in S:
        if e != 1: continue
        for T in marked_patterns(lam, idx):
            Pp, B0, Bs = T; t2 = len(B0) - len(lam) - 1
            check("B3 r=%d m=%d lam=%s" % (r, m, lam), t2 >= 0 and t2 % 2 == 0 and m == 2 * len(Pp) + t2 + sum(lam) + 1)
    # (C1), (C2) for random permutations
    for (lam, e) in S:
        if e != 1: continue
        pats = marked_patterns(lam, idx)
        for T in random.sample(pats, min(len(pats), 6)):
            g = marked_product(R, h, lam, T)
            sig = idx[:]; random.shuffle(sig)
            Pp, B0, Bs = T
            T2 = (tuple((sig[a], sig[b]) for a, b in Pp), tuple(sorted(sig[b] for b in B0)), tuple(tuple(sig[b] for b in B) for B in Bs))
            g2 = marked_product(R, h, lam, T2)
            check("C2 r=%d m=%d p=%d lam=%s" % (r, m, p, lam), eqpm(R, relabel(R, g, sig), g2) != 0)
            c1 = eqpm(R, relabel(R, mPf(R, h, len(lam), sorted(B0)), sig), mPf(R, h, len(lam), sorted(sig[b] for b in B0)))
            check("C1 r=%d m=%d p=%d lam=%s" % (r, m, p, lam), c1 != 0)
    # (D3): Lemma 8.7 in the ring, on every set B of the right size
    for l in range(0, h + 1):
        for sz in range(l + 1, m + 1, 2):
            for B in itertools.combinations(idx, sz):
                target = mPf(R, h, l, list(B))
                gens = []
                for Ssub in itertools.combinations(B, l + 1):
                    rest = [x for x in B if x not in Ssub]
                    for Q in kpairs(rest, len(rest) // 2):
                        gens.append(R.prod([R.vdm(Ssub)] + [R.D(a, b) for a, b in Q]))
                bas = R.ideal(gens)
                check("D3 r=%d m=%d p=%d l=%d B=%s" % (r, m, p, l, B), R.member(bas, target))
    if (r, m, p) in ((3, 5, 101), (5, 4, 101), (7, 3, 101)):
        # control for (D3): the target plus one monomial of its degree
        for l in range(0, h + 1):
            for sz in range(l + 3, m + 1, 2):
                B = tuple(range(sz)); target = mPf(R, h, l, list(B))
                if not target.any(): continue
                # a monomial of the degree of the target that is not in the ideal U_{l+1}: the control «target + monomial»
                d = R.hdeg(target)
                gens1 = []
                for Ssub in itertools.combinations(B, l + 1):
                    rest = [x for x in B if x not in Ssub]
                    for Q in kpairs(rest, len(rest) // 2):
                        gens1.append(R.prod([R.vdm(Ssub)] + [R.D(a, b) for a, b in Q]))
                bas1 = R.ideal(gens1)
                mono = R.zero(); k = int(R.cols[d][0]); mono.reshape(-1)[k] = 1
                control("D3 target + first monomial of its degree, r=%d l=%d |B|=%d" % (r, l, sz), not R.member(bas1, (target + mono) % p))
    # the count: dim V_Lambda = |Z_Lambda| for every interlaced pair
    IP = interlaced_pairs(m, h); eq = 0
    for L in IP:
        gens = gens_VS(R, h, L, idx)
        dV = R.dim(R.ideal(gens)); Z = Zsize(L, m, h)
        check("count r=%d m=%d p=%d L=%s: dim %d, |Z| %d" % (r, m, p, sorted(L), dV, Z), dV == Z)
        eq += (dV == Z)
        # (B5): the unmarked part alone is Tight.VLam of the component 0
        if all(e == 0 for (lam, e) in L):
            g0 = [x for (lam, e) in L for x in pattern_products(R, (lam, 0), idx)]
            check("B5 r=%d m=%d" % (r, m), R.dim(R.ideal(g0)) == dV)
    tot_pairs += len(IP); tot_eq += eq
    # controls on the count, on the interlaced pairs OTHER than Sh_m (for Sh_m the ideal is the whole ring and nothing can fail):
    # (i) D^- in the place of D in the pairs of the marked patterns; (ii) no absorbed pairs (only t = 0 in the marked block)
    if m >= 3:
        bad1 = 0; bad2 = 0; tried = 0
        for L in IP:
            if L == frozenset(S) or not any(e == 1 for (lam, e) in L): continue
            tried += 1; Z = Zsize(L, m, h)
            bad1 += (R.dim(R.ideal(gens_VS(R, h, L, idx, pairfun=R.Bk))) != Z)
            g2 = []
            for (lam, e) in L:
                if e == 0: g2 += pattern_products(R, (lam, 0), idx)
                else:
                    for T in marked_patterns(lam, idx):
                        if len(T[1]) == len(lam) + 1: g2.append(marked_product(R, h, lam, T))
            bad2 += (R.dim(R.ideal(g2)) != Z)
        control("count with D^- in the pairs of the marked patterns, r=%d m=%d p=%d: wrong in %d of %d pairs" % (r, m, p, bad1, tried), bad1 > 0)
        control("count without absorbed pairs (t = 0 only), r=%d m=%d p=%d: wrong in %d of %d pairs" % (r, m, p, bad2, tried), bad2 > 0)
    print("cell r=%d m=%d p=%d: interlaced pairs %d, equal %d" % (r, m, p, len(IP), eq)); sys.stdout.flush()

print("interlaced pairs in all: %d, with dim = |Z|: %d" % (tot_pairs, tot_eq))
print("TOTAL checks %d, failures %d; controls %d, fire %d" % (NCHK, NFAIL, NCTL, NFIRE))
print("FIN-OK" if NFAIL == 0 else "FIN-CON-FALLOS")
