#!/usr/bin/env python3
"""
ref7a_chain_coverage.py -- brute-force check of PAPER_OFICIAL_v6, section 7.1-7.3.

Tests (all independent of the paper's own engines):
  T0  binomial claim: C(q-1,t) == (-1)^t mod p for q = p^v; also reports, for some odd q
      that are not powers of p, whether the standing hypothesis C(q-1,t) != 0 holds
      (by Lucas it holds iff q = a*p^k with 1 <= a < p; the paper only says 'for instance').
  T1  'every element of BPar_q(alpha,beta) is the shape of some point' (set equality of
      the shapes of all points of Omega^alpha x Omega^beta with BPar_q(alpha,beta)).
  T2  (P1): for every tail M' in Omega^(alpha-1) x Omega^beta the multiset of shapes
      lambda(u,M'), u in Omega, equals the multiset {opt_p(mu) : p=1..q} of section 7.3,
      and every option lies in BPar_q(alpha,beta) (including the middle option).
  T3  (Chain), Lemma 7.3: opt_1 <= opt_2 <= ... <= opt_q in the product order, for every
      tail shape mu in BPar_q(alpha-1,beta).
  T4  For every down-set Lambda of BPar_q(alpha,beta) (product order) and every tail shape
      mu: the options in Lambda form an initial segment; r, iota, j_0 are as described
      (r = 0 or last row of its length; j_0 first row of its length; additions in Lambda
      exactly for j_0 <= j <= l_+); the side claims (j_0 exists => r = l_- and
      (iota = 1 or l_+ + l_- = q); iota = 1 => r = l_-); formula (7.1); and the
      trichotomy Phi = q - j_0 + 1 / q - l_+ / r.
  T5  Lemma 7.1(iv) with Z_{>i} = Z_{Lambda_i}: |Z_Lambda| = sum_i |Z_{Lambda_i}| for every
      down-set (computed from point counts per shape), and Lambda_i is a set of shapes of
      BPar_q(alpha-1,beta).
  T6  Lemma 7.2: the down-sets {(empty,empty)} and {((1),empty)}; the counts
      N_bal(a,3) = 3,15,93,639,4653; N_bal(2,q) = 15,45,91,153,231; the closed formula
      sum (multinomial)^2; N_ph(a,q) = N_bal(a+1,q).
Cells: q in {3,5}, alpha in {1,2,3}, beta in {0,1,2,3}; with the argument 'ext': q in {3,5,7,9}, alpha in 1..4, beta in 0..4, alpha+beta <= 7,6,5,4 respectively.
"""
import itertools, sys, time
from collections import Counter
from math import comb, factorial

t_start = time.time()
FAIL = 0
def fail(msg):
    global FAIL
    FAIL += 1
    print("FAIL:", msg)

# ---------- partitions and orders ----------
def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0:
        yield (); return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest

def S(lam, t): return sum(lam[:t])
def dom(lam, mu):
    T = max(len(lam), len(mu), 1)
    return all(S(lam, t) <= S(mu, t) for t in range(1, T + 1))
def pdom(a, b): return dom(a[0], b[0]) and dom(a[1], b[1])

def shape(xs, zs):
    cx, cz = Counter(xs), Counter(zs)
    keys = set(cx) | set(cz)
    plus = sorted((cx[u] - cz[u] for u in keys if cx[u] > cz[u]), reverse=True)
    minus = sorted((cz[u] - cx[u] for u in keys if cz[u] > cx[u]), reverse=True)
    return (tuple(plus), tuple(minus))

def BPar(q, a, b):
    out = []
    for sp in range(0, a + 1):
        sm = sp - (a - b)
        if sm < 0 or sm > b: continue
        for lp in partitions(sp):
            for lm in partitions(sm):
                if len(lp) + len(lm) <= q:
                    out.append((lp, lm))
    return out

def remove_box(lam, j):
    l = list(lam); l[j - 1] -= 1
    return tuple(sorted([x for x in l if x > 0], reverse=True))
def add_box(lam, j):
    l = list(lam); l[j - 1] += 1
    return tuple(sorted(l, reverse=True))
def add_one(lam): return tuple(sorted(list(lam) + [1], reverse=True))

def options(q, mu):
    """opt_p(mu), p = 1..q, exactly as in section 7.3."""
    mp, mm = mu; lp, lm = len(mp), len(mm)
    opts = []
    for p in range(1, q + 1):
        if p <= lm: opts.append((mp, remove_box(mm, p)))
        elif p <= q - lp: opts.append((add_one(mp), mm))
        else: opts.append((add_box(mp, q + 1 - p), mm))
    return opts

def rbar(lam, j):
    v = lam[j - 1]; return max(i + 1 for i in range(len(lam)) if lam[i] == v)
def runder(lam, j):
    v = lam[j - 1]; return min(i + 1 for i in range(len(lam)) if lam[i] == v)

def downsets(P):
    """All down-sets of the finite poset P (list of elements) for pdom, as frozensets."""
    n = len(P)
    below = []
    for i, a in enumerate(P):
        m = 0
        for j, b in enumerate(P):
            if pdom(b, a): m |= (1 << j)
        below.append(m)
    out = []
    for mask in range(1 << n):
        ok = True
        mm = mask
        while mm:
            i = (mm & -mm).bit_length() - 1
            if below[i] & ~mask: ok = False; break
            mm &= mm - 1
        if ok:
            out.append(frozenset(P[i] for i in range(n) if mask >> i & 1))
    return out

# ---------- T0: binomials ----------
print("== T0: C(q-1,t) mod p ==")
for (q, p) in [(3, 3), (5, 5), (7, 7), (9, 3), (25, 5), (27, 3), (81, 3), (49, 7)]:
    bad = [t for t in range(q) if comb(q - 1, t) % p != (-1) ** t % p]
    if bad: fail(f"q={q}, p={p}: C(q-1,t) != (-1)^t mod p at t={bad}")
    else: print(f"  q={q}=p^v, p={p}: C(q-1,t) == (-1)^t mod p for all 0<=t<=q-1  OK")
for (q, p) in [(15, 3), (15, 5), (21, 3), (21, 7), (45, 3), (45, 5)]:
    zeros = [t for t in range(q) if comb(q - 1, t) % p == 0]
    verdict = "standing hypothesis FAILS" if zeros else "standing hypothesis holds (q = a*p^k, a < p; Lucas)"
    print(f"  q={q} (not a power of p={p}): C(q-1,t) == 0 mod p at t={zeros[:6]}{'...' if len(zeros)>6 else ''}  -> {verdict}")

# ---------- T6 (part): N_bal, N_ph ----------
print("== T6: Lemma 7.2 counts ==")
def N_bal_formula(a, q):
    tot = 0
    for c in itertools.product(range(a + 1), repeat=q):
        if sum(c) == a:
            m = factorial(a)
            for ci in c: m //= factorial(ci)
            tot += m * m
    return tot
def N_bal_brute(a, q):
    return sum(1 for xs in itertools.product(range(q), repeat=a)
                 for zs in itertools.product(range(q), repeat=a)
                 if sorted(xs) == sorted(zs))
def N_ph_brute(a, q):
    def sub(Y, X):
        cy, cx = Counter(Y), Counter(X)
        return all(cx[u] >= cy[u] for u in cy)
    return sum(1 for xs in itertools.product(range(q), repeat=a + 1)
                 for zs in itertools.product(range(q), repeat=a)
                 if sub(zs, xs))
vals = [N_bal_brute(a, 3) for a in range(1, 6)]
print("  N_bal(a,3), a=1..5 (brute):", vals)
if vals != [3, 15, 93, 639, 4653]: fail("N_bal(a,3) list")
vals2 = [N_bal_brute(2, q) for q in (3, 5, 7, 9, 11)]
print("  N_bal(2,q), q=3..11 (brute):", vals2)
if vals2 != [15, 45, 91, 153, 231]: fail("N_bal(2,q) list")
for (a, q) in [(1, 3), (2, 3), (3, 3), (4, 3), (1, 5), (2, 5), (3, 5), (2, 7)]:
    if N_bal_formula(a, q) != N_bal_brute(a, q): fail(f"N_bal formula at {(a,q)}")
for (a, q) in [(0, 3), (1, 3), (2, 3), (3, 3), (0, 5), (1, 5), (2, 5), (1, 7)]:
    nph, nb1 = N_ph_brute(a, q), N_bal_brute(a + 1, q)
    if nph != nb1: fail(f"N_ph(a,q) != N_bal(a+1,q) at {(a,q)}: {nph} vs {nb1}")
print("  closed formula and N_ph(a,q) = N_bal(a+1,q): OK at the tested cells")
for q in (3, 5):
    for a in (0, 1, 2, 3):
        P = BPar(q, a, a)
        if [x for x in P if pdom(x, ((), ()))] != [((), ())]: fail(f"root bal down-set q={q} a={a}")
        P2 = BPar(q, a + 1, a)
        if sorted(x for x in P2 if pdom(x, ((1,), ()))) != [((1,), ())]: fail(f"root ph down-set q={q} a={a}")
print("  {(0,0)} and {((1),0)} are down-sets with no other element below: OK")

# ---------- main cells ----------
print("== T1-T5 over the cells ==")
tot_downsets = tot_checks = tot_tails = 0
EXT = "ext" in sys.argv[1:]
if EXT:
    CELLS = [(a, b, q) for q, smax in ((3, 7), (5, 6), (7, 5), (9, 4)) for a in range(1, 5) for b in range(0, 5) if a + b <= smax]
else:
    CELLS = [(a, b, q) for q in (3, 5) for a in (1, 2, 3) for b in (0, 1, 2, 3)]
print("mode:", "extended" if EXT else "base", "cells:", len(CELLS))
for (alpha, beta, q) in CELLS:
    Omega = range(q)
    if True:
        if True:
            P = BPar(q, alpha, beta)          # target family
            if len(P) > 20:
                print(f"  cell ({alpha},{beta},{q}) skipped: |BPar|={len(P)} > 20"); continue
            Pt = BPar(q, alpha - 1, beta)     # tail family
            Pset, Ptset = set(P), set(Pt)
            # T1: shapes of points == BPar
            cnt = Counter(shape(xs, zs) for xs in itertools.product(Omega, repeat=alpha)
                                          for zs in itertools.product(Omega, repeat=beta))
            if set(cnt) != Pset: fail(f"T1 cell {(alpha,beta,q)}: shapes {set(cnt)^Pset}")
            cnt_t = Counter(shape(xs, zs) for xs in itertools.product(Omega, repeat=alpha - 1)
                                            for zs in itertools.product(Omega, repeat=beta))
            if set(cnt_t) != Ptset: fail(f"T1 tail cell {(alpha-1,beta,q)}")
            # T2: (P1) on every tail
            ntails = 0
            for xs in itertools.product(Omega, repeat=alpha - 1):
                for zs in itertools.product(Omega, repeat=beta):
                    ntails += 1
                    mu = shape(xs, zs)
                    real = Counter(shape((u,) + xs, zs) for u in Omega)
                    pred = Counter(options(q, mu))
                    if real != pred: fail(f"T2 (P1) cell {(alpha,beta,q)} tail {(xs,zs)}: {real} vs {pred}")
            tot_tails += ntails
            # T2 (membership) and T3 (chain) per tail shape
            for mu in Pt:
                opts = options(q, mu)
                if len(opts) != q: fail("option count")
                for o in opts:
                    if o not in Pset: fail(f"T2 option {o} of {mu} not in BPar {(alpha,beta,q)}")
                    if len(o[0]) + len(o[1]) > q: fail("length constraint")
                for p in range(q - 1):
                    if not pdom(opts[p], opts[p + 1]):
                        fail(f"T3 chain cell {(alpha,beta,q)} mu={mu}: opt_{p+1}={opts[p]} !<= opt_{p+2}={opts[p+1]}")
            # T4/T5 over all down-sets
            DS = downsets(P)
            tot_downsets += len(DS)
            for Lam in DS:
                Z_L = sum(cnt[l] for l in Lam)
                sumF = 0
                for mu in Pt:
                    mp, mm = mu; lp, lm = len(mp), len(mm)
                    opts = options(q, mu)
                    inL = [o in Lam for o in opts]
                    F = sum(inL)
                    if inL != [True] * F + [False] * (q - F):
                        fail(f"T4 not initial segment {(alpha,beta,q)} Lam={sorted(Lam)} mu={mu}: {inL}")
                    # r
                    r = 0
                    while r < lm and (mp, remove_box(mm, r + 1)) in Lam: r += 1
                    if not (r == 0 or rbar(mm, r) == r): fail(f"T4 r not last row of its length {mu} r={r}")
                    # iota
                    if lp + lm < q:
                        iota = 1 if (add_one(mp), mm) in Lam else 0
                    else:
                        iota = 0
                        if (add_one(mp), mm) in Lam: fail("middle option in Lam although no middle position")
                    # j0
                    adds = [(add_box(mp, j), mm) in Lam for j in range(1, lp + 1)]
                    j0 = None
                    if any(adds):
                        j0 = min(j for j in range(1, lp + 1) if adds[j - 1])
                        if not all(adds[j - 1] for j in range(j0, lp + 1)): fail(f"T4 additions not a final range {mu}")
                        if runder(mp, j0) != j0: fail(f"T4 j0 not first row of its length {mu} j0={j0}")
                        # side claim
                        if r != lm: fail(f"T4 side claim: j0 exists but r={r} != l_-={lm}, mu={mu}")
                        if not (iota == 1 or lp + lm == q): fail(f"T4 side claim: j0 exists, iota=0, l_+ + l_- < q, mu={mu}")
                    if iota == 1 and r != lm: fail(f"T4 side claim: iota=1 but r != l_-, mu={mu}")
                    F71 = r + (q - lp - lm) * iota + ((lp - j0 + 1) if j0 else 0)
                    if F71 != F: fail(f"T4 (7.1) cell {(alpha,beta,q)} Lam={sorted(Lam)} mu={mu}: F={F} formula={F71}")
                    Phi = (q - j0 + 1) if j0 else ((q - lp) if iota == 1 else r)
                    if Phi != F: fail(f"T4 trichotomy {mu}: F={F} Phi={Phi}")
                    sumF += cnt_t[mu] * F
                    tot_checks += 1
                # T5: |Z_Lambda| = sum_i |Z_{Lambda_i}| = sum_tails F
                if Z_L != sumF: fail(f"T5 cell {(alpha,beta,q)} Lam={sorted(Lam)}: |Z|={Z_L} sum={sumF}")
            print(f"  cell (alpha,beta,q)=({alpha},{beta},{q}): |BPar|={len(P):2d}, |BPar tail|={len(Pt):2d}, "
                  f"down-sets={len(DS):5d}, tails={ntails:5d}: T1-T5 done, failures so far={FAIL}")
print(f"TOTAL: down-sets={tot_downsets}, (7.1)-checks (Lambda,mu)={tot_checks}, tails={tot_tails}, FAILURES={FAIL}")
print(f"elapsed {time.time() - t_start:.2f} s")
sys.exit(1 if FAIL else 0)
