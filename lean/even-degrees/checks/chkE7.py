# chkE7.py -- brute force for piece E7 (q_oddbox_layers.md), paper v11 §8.2: Lemma 8.4 (layers) and Lemma 8.5 (roots).
# Grepy Mandalay, 2 Oct 2026.  Own code; the partition/shape functions are those of chkE6.py (they mirror the LEAN definitions).
# ESTIMATE WRITTEN BEFORE RUNNING: pure Python, small tuples.
#   Enumeration of all interlaced pairs: all subsets of Sh_m with |Sh_m| <= 16 (65 536 subsets), as in chkE6 (4 s).
#   Per pair: (L1), (L2), (E), (L3) over Sh_{m-1} x rows x positions: a few thousand operations.  < 60 s in all.
#   (L4), (L5) by points: r^m <= 3^7 = 2187, 5^5 = 3125, 7^4 = 2401 tuples per pair, <= 60 pairs per cell: < 60 s.
#   Roots: closed tuples by enumeration, r^(2k+2) <= 3^8 = 6561, 5^6 = 15625, 7^4 = 2401: < 10 s.
#   Memory < 100 MB.  Inside vigia.sh with the default cap (1.2 GB / 600 s).
import itertools, sys
from collections import Counter
from math import factorial

FAILS = 0; CHECKS = 0
def check(name, ok):
    global FAILS, CHECKS
    CHECKS += 1
    if not ok: FAILS += 1
    print(('ok   ' if ok else 'FAIL ') + name); sys.stdout.flush()

# ---------------------------------------------------------------- partitions and shapes, as in chkE6.py
def subE(mu, j):
    l = list(mu); l[j - 1] -= 1
    return tuple(sorted([x for x in l if x != 0], reverse=True))
def addE(mu, j):
    l = list(mu); l[j - 1] += 1
    return tuple(sorted(l, reverse=True))
def addOne(mu): return tuple(mu) + (1,)
def opt(mu, L, p):
    l = len(mu)
    if p <= l: return subE(mu, p)
    if p <= L - l: return addOne(mu)
    return addE(mu, L + 1 - p)
def optS(mu, d, h, p):           # LEAN: OddShapes.optS h (mu, d) p, p = 1..2h+1
    l = len(mu)
    if p <= l: return (subE(mu, p), d)
    if p == l + 1: return (mu, 1 - d)
    if p <= 2 * h + 1 - l: return (addOne(mu), d)
    return (addE(mu, 2 * h + 2 - p), d)
def wdom(a, b):
    sa = sb = 0
    for t in range(max(len(a), len(b))):
        sa += a[t] if t < len(a) else 0; sb += b[t] if t < len(b) else 0
        if sa > sb: return False
    return True
def partitions_le(n, h):
    out = [()]
    def rec(pref, rem, mx):
        for x in range(min(rem, mx), 0, -1):
            q = pref + (x,); out.append(q)
            if len(q) < h: rec(q, rem - x, x)
    if h > 0: rec((), n, n)
    return out
def Par(h, n): return [l for l in partitions_le(n, h) if sum(l) % 2 == n % 2]
def Sh(h, m): return [(l, 0) for l in Par(h, m)] + ([(l, 1) for l in Par(h, m - 1)] if m >= 1 else [])
def setting(h): return [0] + [u for i in range(1, h + 1) for u in (i, -i)]
def shape(M, T):
    c = Counter(M)
    parts = sorted([c[u] - c[-u] for u in T if u != 0 and c[u] - c[-u] > 0], reverse=True)
    return (tuple(parts), c[0] % 2)
def FLam(h, Lam, mu): return sum(1 for p in range(1, 2 * h + 1) if opt(mu, 2 * h, p) in Lam)
def FS(h, Lam, mu, d):           # LEAN: OddShapes.FS h Lam (mu, d)   (8.5)
    Ld = {l for (l, e) in Lam if e == d}; Lo = {l for (l, e) in Lam if e == 1 - d}
    return FLam(h, Ld, mu) + (1 if mu in Lo else 0)
def is_downset_par(h, n, A):
    P = Par(h, n); Ps = set(P)
    return all(a in Ps for a in A) and all(l in A for mu in A for l in P if wdom(l, mu))
def is_interlaced(h, m, Lam):    # LEAN: OddShapes.IsInterlaced h m Lam  (m - 1 is the truncated subtraction)
    S = set(Sh(h, m))
    if not all(s in S for s in Lam): return False
    L0 = {l for (l, e) in Lam if e == 0}; L1 = {l for (l, e) in Lam if e == 1}
    if not is_downset_par(h, m, L0): return False
    if not is_downset_par(h, max(m - 1, 0), L1): return False
    return all((subE(nu, j), 1 - d) in Lam for (nu, d) in Lam for j in range(1, len(nu) + 1))
def is_d1_only(h, m, Lam):
    L0 = {l for (l, e) in Lam if e == 0}; L1 = {l for (l, e) in Lam if e == 1}
    return all(s in set(Sh(h, m)) for s in Lam) and is_downset_par(h, m, L0) and is_downset_par(h, max(m - 1, 0), L1)
def all_subsets(S):
    for bits in range(1 << len(S)):
        yield frozenset(S[i] for i in range(len(S)) if bits >> i & 1)
def layer(h, m, Lam, i):         # the layer Lambda_i := {sigma in Sh_{m-1} : F_Lambda(sigma) > i}
    return frozenset(s for s in Sh(h, m - 1) if FS(h, Lam, s[0], s[1]) > i)

# the explicit position p' of the proof of (E) in q_oddbox_layers.md
def pprime(h, nu, j, p):
    l = len(nu); a = nu[j - 1]; nup = subE(nu, j); lp = len(nup)
    jstar = max(i for i in range(1, l + 1) if nu[i - 1] == a)            # last row of length a
    if p <= l:
        if nu[p - 1] == a: return lp + 1
        return max(i for i in range(1, l + 1) if nu[i - 1] == nu[p - 1])  # last row of the length of row p
    if p == l + 1:
        return 2 * h + 2 - jstar if a >= 2 else l + 1
    if p <= 2 * h + 1 - l:
        return 2 * h + 1 - lp
    i = 2 * h + 2 - p
    i0 = min(t for t in range(1, l + 1) if nu[t - 1] == nu[i - 1])        # first row of the length of row i
    if nu[i - 1] != a: return 2 * h + 2 - i0
    if i0 < jstar: return 2 * h + 2 - i0
    return 2 * h + 2 - jstar if a >= 2 else 2 * h + 1 - lp

CELLS = [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]
PAIRS = {}
tot = 0
for (h, m) in CELLS:
    PAIRS[(h, m)] = [L for L in all_subsets(Sh(h, m)) if is_interlaced(h, m, L)]
    tot += len(PAIRS[(h, m)])
check('enumerator: %d interlaced pairs in the 18 cells (chkE6: 163)' % tot, tot == 163)

# ---------------------------------------------------------------- Lemma 8.4
nL1 = nL2 = nE = nL3 = 0
for (h, m) in CELLS:
    r = 2 * h + 1; ShT = Sh(h, m - 1); okL1 = okL2 = okE = okEx = okL3 = okTop = True
    for Lam in PAIRS[(h, m)]:
        F = {s: FS(h, Lam, s[0], s[1]) for s in ShT}
        # (L1) monotone in each component
        for (mu, d) in ShT:
            for (mt, dt) in ShT:
                if d == dt and wdom(mu, mt):
                    nL1 += 1
                    if F[(mt, d)] > F[(mu, d)]: okL1 = False
        # (L2) and (E)
        for (nu, d) in ShT:
            for j in range(1, len(nu) + 1):
                nup = subE(nu, j); nL2 += 1
                if (nup, 1 - d) not in F: okL2 = False; continue
                if F[(nu, d)] > F[(nup, 1 - d)]: okL2 = False
                for p in range(1, r + 1):
                    if optS(nu, d, h, p) in Lam:
                        nE += 1
                        if not any(optS(nup, 1 - d, h, pp) in Lam for pp in range(p, r + 1)): okE = False
                        pp = pprime(h, nu, j, p)
                        if not (p <= pp <= r and optS(nup, 1 - d, h, pp) in Lam): okEx = False
        # (L3) every layer is an interlaced pair of level m - 1; (L3') the layers decrease; layer r is empty
        prev = None
        for i in range(0, r + 1):
            Li = layer(h, m, Lam, i); nL3 += 1
            if not is_interlaced(h, m - 1, Li): okL3 = False
            if prev is not None and not Li <= prev: okL3 = False
            prev = Li
        if layer(h, m, Lam, r): okTop = False
    check('(L1) F_Lambda(mu~,d) <= F_Lambda(mu,d) for mu <= mu~ in the same component: h=%d m=%d' % (h, m), okL1)
    check('(L2) F_Lambda(nu,d) <= F_Lambda(nu - e_j, 1-d): h=%d m=%d' % (h, m), okL2)
    check('(E) option p in Lambda => some option p\' >= p of (nu - e_j, 1-d) in Lambda, and the explicit p\' of the proof works: h=%d m=%d' % (h, m), okE and okEx)
    check('(L3) every layer Lambda_i (i = 0..r) is an interlaced pair of level m-1, decreasing in i, empty at i = r: h=%d m=%d' % (h, m), okL3 and okTop)
print('   cases: (L1) %d, (L2) %d, (E) %d, (L3) %d layers' % (nL1, nL2, nE, nL3))

# (L4), (L5) by points
for (h, m) in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3)]:
    T = setting(h); r = 2 * h + 1; ok4 = ok5 = True; n = 0
    tails = list(itertools.product(T, repeat=m - 1)); shp = {Mp: shape(Mp, T) for Mp in tails}
    comp = {Mp: Counter(shape((t,) + Mp, T) for t in T) for Mp in tails}
    for Lam in PAIRS[(h, m)]:
        cnt = {Mp: sum(v for s, v in comp[Mp].items() if s in Lam) for Mp in tails}      # completions in Z_Lambda
        Z = sum(cnt.values()); tot_layers = 0
        for i in range(0, r):
            Li = layer(h, m, Lam, i); n += 1
            Zgt = {Mp for Mp in tails if cnt[Mp] > i}
            ZLi = {Mp for Mp in tails if shp[Mp] in Li}
            if Zgt != ZLi: ok4 = False
            tot_layers += len(ZLi)
        if Z != tot_layers: ok5 = False
    check('(L4) (Z_Lambda)_{>i} = Z_{Lambda_i} by points, every interlaced pair, i = 0..r-1: h=%d m=%d (%d layers)' % (h, m, n), ok4)
    check('(L5) |Z_Lambda| = sum_i |Z_{Lambda_i}|: h=%d m=%d' % (h, m), ok5)

# ---------------------------------------------------------------- Lemma 8.5 (roots)
def QkEven(k, m):                # LEAN: EvenCount.QkEven k m, h = (m-2)/2
    h = (m - 2) // 2; N = 2 * k + 2; tot = 0
    def rec(u, rem, den):
        nonlocal tot
        if u == h:
            c = rem                                   # 2c + 2 sum b = N
            tot += factorial(N) // (factorial(2 * c) * den)
            return
        for b in range(0, rem + 1): rec(u + 1, rem - b, den * factorial(b) ** 2)
    rec(0, k + 1, 1)
    return tot
EVEN = frozenset([((), 0)]); ODD = frozenset([((1,), 0), ((), 1)])
for (h, k) in [(1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]:
    T = setting(h); r = 2 * h + 1; N = 2 * k + 2
    closed = 0; zeven = 0
    for M in itertools.product(T, repeat=N):
        c = Counter(M)
        cl = all(c[u] == c[-u] for u in T) and c[0] % 2 == 0
        closed += cl
        zeven += (shape(M, T) == ((), 0))
        if cl != (shape(M, T) == ((), 0)): closed = -10 ** 9
    zodd = sum(1 for M in itertools.product(T, repeat=N - 1) if shape(M, T) in ODD)
    Q = QkEven(k, 2 * h + 2)
    check('(R1),(R2),(R4) h=%d k=%d: Z_{(0,0)} at level %d = closed tuples; |.| = %d = QkEven k (2h+2) = %d; |Z_root| at level %d = %d'
          % (h, k, N, zeven, Q, N - 1, zodd), closed == zeven == Q == zodd)
    # (R3) the layers of the even root
    L0 = layer(h, N, EVEN, 0); L1 = layer(h, N, EVEN, 1)
    check('(R3) h=%d k=%d: layer 0 of {(empty,0)} at level %d is {((1),0),(empty,1)}, layer 1 is empty' % (h, k, N), L0 == ODD and not L1)
vals = [QkEven(1, 4), QkEven(2, 4), QkEven(1, 6), QkEven(2, 6), QkEven(1, 8)]
print('   QkEven: (k,m) = (1,4),(2,4),(1,6),(2,6),(1,8):', vals)
check('values N_3(4) = 19, N_3(6) = 141, N_5(4) = 61 (paper v11 gate: 19, 141, 61)', vals[0] == 19 and vals[1] == 141 and vals[2] == 61)

# ---------------------------------------------------------------- controls (expected outcomes computed by hand, see the comments)
# K1: for Lambda = Sh_m, F_Lambda(sigma) = 2h+1 for every sigma in Sh_{m-1} ((B3)); a "layer" defined with F* alone
#     (forgetting the zero option, F* <= 2h) is EMPTY at i = 2h while the true layer is Sh_{m-1}.  Must differ in every cell.
k1 = 0
for (h, m) in CELLS:
    Lam = frozenset(Sh(h, m)); i = 2 * h
    wrong = frozenset((mu, d) for (mu, d) in Sh(h, m - 1) if FLam(h, {l for (l, e) in Lam if e == d}, mu) > i)
    if wrong != layer(h, m, Lam, i): k1 += 1
check('control K1: layers defined without the zero option differ at i = 2h for Lambda = Sh_m (in %d of %d cells)' % (k1, len(CELLS)), k1 == len(CELLS))
# K2: the unmarked half of the odd root alone, {((1),0)}: the tuples with one unpaired ZERO are missing; e.g. (0) at level 1.
k2 = 0; k2n = 0
for (h, k) in [(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0), (3, 1)]:
    T = setting(h); k2n += 1
    z = sum(1 for M in itertools.product(T, repeat=2 * k + 1) if shape(M, T) == ((1,), 0))
    if z < QkEven(k, 2 * h + 2): k2 += 1
check('control K2: |Z_{((1),0)}| at level 2k+1 is strictly smaller than N_r(2k+2) (in %d of %d cells)' % (k2, k2n), k2 == k2n)
# K3: (L2) WITHOUT (D2).  Lambda = {((1),0)} at an odd level m >= 3, h >= 1: both components are down-sets, (D2) fails
#     (it lacks (empty,1)).  Take nu = (1), d = 1 in Sh_{m-1} (|nu| + d = 2 <= m-1, parity of m-1), j = 1: nu - e_1 = empty.
#     F(nu, 1) = F*_{empty set}(nu) + [(1) in Lambda^0] = 0 + 1 = 1;  F(empty, 0) = F*_{Lambda^0}(empty) + [empty in Lambda^1]
#     = #{p <= 2h : opt_p(empty) = (1)} + 0 = 2h.  So (L2) HOLDS here (1 <= 2h): this is not a counterexample.
#     Counterexample computed by hand: Lambda = {(empty,1)} at an even level m >= 2 ((D2) holds vacuously -- so it IS interlaced
#     only if (D1) holds, and it does).  So instead the control is run over ALL pairs of down-sets that are not interlaced,
#     and it only REPORTS how many violate (L2) or have a non-interlaced layer; no expectation is asserted for (L2).
rep = []
for (h, m) in [(1, 3), (1, 4), (2, 3), (2, 4), (3, 3)]:
    d1 = [L for L in all_subsets(Sh(h, m)) if is_d1_only(h, m, L) and not is_interlaced(h, m, L)]
    v2 = 0; v3 = 0
    for Lam in d1:
        ShT = Sh(h, m - 1); F = {s: FS(h, Lam, s[0], s[1]) for s in ShT}
        if any(F[(nu, d)] > F[(subE(nu, j), 1 - d)] for (nu, d) in ShT for j in range(1, len(nu) + 1)): v2 += 1
        if any(not is_interlaced(h, m - 1, layer(h, m, Lam, i)) for i in range(0, 2 * h + 1)): v3 += 1
    rep.append((h, m, len(d1), v2, v3))
print('   report K3 (pairs of down-sets without (D2)): (h, m, how many, violate (L2), have a non-interlaced layer):', rep)
print('TOTAL checks %d, failures %d' % (CHECKS, FAILS))
print('FIN-OK')
