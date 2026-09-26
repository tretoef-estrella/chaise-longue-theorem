#!/usr/bin/env python3
"""
sec74_prop74_bruteforce.py -- referee check of PAPER_OFICIAL_v6.md, section 7.4
(Lemma 7.3', Proposition 7.4), plus the pieces of section 7.3 / 5.5 that it rests on.

Everything is re-implemented from the definitions (no code of the author is used):
  * weak dominance  lam <= mu  iff  S_t(lam) <= S_t(mu) for all t;
  * BPar_q(a,b) = pairs (l+,l-) with |l+|-|l-| = a-b, |l+|+|l-| <= a+b, len(l+)+len(l-) <= q;
  * opt_p(mu) for p = 1..q as in section 7.3 (R for p <= l-, M for l- < p <= q-l+, A else, j = q+1-p).

Checks:
  C0  the section-5.5 identities  S_t(mu-e_j) = S_t(mu) - [t >= rbar_j],  S_t(mu+e_j) = S_t(mu) + [t >= runder_j],
      S_t(mu u 1) = S_t(mu) + [t > l]   (used in every case of Prop. 7.4), on all partitions of size <= 12.
  C1  Lemma 7.3 (chain)  opt_1 <= ... <= opt_q  and membership of every option in BPar_q(alpha,beta), every tail shape.
  C2  Proposition 7.4, first sentence:  for every ordered pair mu <= mut in BPar_q(alpha-1,beta), every p:
      opt_p(mu) <= opt_p(mut) (product order).  Also tallies which of the nine cases each (pair,p) falls in,
      and checks the auxiliary claims used inside the proof (MR/AR: |mut-| >= |mu-|+1 and |mut+| >= |mu+|+1;
      AR: l- < p and lt+ <= j-1).
  C3  (P1) by brute force on small cells: for every tail M' the multiset {shape(u,M') : u in Omega}
      equals the multiset {opt_p(shape(M')) : p = 1..q}.
  C4  Proposition 7.4, second sentence, directly: for every down-set Lambda of BPar_q(alpha,beta) (small cells only),
      F_Lambda is order-reversing and every Lambda_i is a down-set; and the coverage formula (7.1) / the
      'in particular' formula after Lemma 7.3 agree with the direct count.
"""
import sys, time, itertools
from collections import Counter

t_start = time.time()

# ---------- partitions ----------
def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0:
        yield ()
        return
    for first in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest

def S(lam, t):
    return sum(lam[:t])

def dom(lam, mu):
    """weak dominance lam <= mu : S_t(lam) <= S_t(mu) for all t >= 1 (partitions of any sizes)."""
    T = max(len(lam), len(mu))
    a = b = 0
    for t in range(T):
        a += lam[t] if t < len(lam) else 0
        b += mu[t] if t < len(mu) else 0
        if a > b:
            return False
    return True

def pdom(x, y):
    return dom(x[0], y[0]) and dom(x[1], y[1])

def remove_box(lam, p):           # p is a 1-based row index, 1 <= p <= len(lam)
    l = list(lam); l[p-1] -= 1
    return tuple(sorted([v for v in l if v > 0], reverse=True))

def add_box(lam, j):              # 1 <= j <= len(lam)
    l = list(lam); l[j-1] += 1
    return tuple(sorted(l, reverse=True))

def add_one(lam):
    return tuple(sorted(list(lam) + [1], reverse=True))

def rbar(lam, j):                 # last row of length lam_j (1-based)
    v = lam[j-1]; r = j
    while r < len(lam) and lam[r] == v: r += 1
    return r

def runder(lam, j):               # first row of length lam_j (1-based)
    v = lam[j-1]; r = j
    while r > 1 and lam[r-2] == v: r -= 1
    return r

# ---------- C0: identities of section 5.5 ----------
def check_C0(maxn=12):
    n_checked = 0; fails = 0
    for n in range(0, maxn+1):
        for lam in partitions(n):
            l = len(lam)
            T = l + 3
            for j in range(1, l+1):
                rm = remove_box(lam, j); ad = add_box(lam, j)
                rb = rbar(lam, j); ru = runder(lam, j)
                for t in range(1, T+1):
                    if S(rm, t) != S(lam, t) - (1 if t >= rb else 0): fails += 1
                    if S(ad, t) != S(lam, t) + (1 if t >= ru else 0): fails += 1
                    n_checked += 2
            a1 = add_one(lam)
            for t in range(1, T+1):
                if S(a1, t) != S(lam, t) + (1 if t > l else 0): fails += 1
                n_checked += 1
    print(f"[C0] section-5.5 identities: {n_checked} instances on all partitions of size <= {maxn}, failures = {fails}")
    return fails

# ---------- BPar and options ----------
def BPar(q, a, b):
    res = []
    for k in range(min(a, b) + 1):
        for lp in partitions(a - k):
            for lm in partitions(b - k):
                if len(lp) + len(lm) <= q:
                    res.append((lp, lm))
    return res

def in_BPar(x, q, a, b):
    lp, lm = x
    return (sum(lp) - sum(lm) == a - b) and (sum(lp) + sum(lm) <= a + b) and (len(lp) + len(lm) <= q)

def opts(mu, q):
    """list over p=1..q of (type, option) exactly as in section 7.3."""
    mp, mm = mu; lp, lm = len(mp), len(mm)
    out = []
    for p in range(1, q + 1):
        if p <= lm:
            out.append(('R', (mp, remove_box(mm, p))))
        elif p <= q - lp:
            out.append(('M', (add_one(mp), mm)))
        else:
            j = q + 1 - p
            out.append(('A', (add_box(mp, j), mm)))
    return out

# ---------- C1: chain and membership ----------
def check_C1(q, a, b):
    """tail shapes in BPar_q(a,b) = BPar_q(alpha-1,beta); options must lie in BPar_q(a+1,b) and form a chain."""
    fails = 0; n = 0
    for mu in BPar(q, a, b):
        O = opts(mu, q)
        for typ, o in O:
            n += 1
            if not in_BPar(o, q, a + 1, b): fails += 1
        for p in range(q - 1):
            if not pdom(O[p][1], O[p+1][1]): fails += 1
    return n, fails

# ---------- C2: Proposition 7.4 first sentence ----------
def check_C2(q, a, b, verbose=False):
    P = BPar(q, a, b)
    OPT = {mu: opts(mu, q) for mu in P}
    case_count = Counter(); fails = []; npairs = 0; npairs_strict = 0; aux_fails = 0
    for mu in P:
        for mut in P:
            if not pdom(mu, mut): continue
            npairs += 1
            if mu != mut: npairs_strict += 1
            lp, lm = len(mu[0]), len(mu[1]); ltp, ltm = len(mut[0]), len(mut[1])
            for p in range(1, q + 1):
                typ, o = OPT[mu][p-1]; typt, ot = OPT[mut][p-1]
                case = typ + typt
                case_count[case] += 1
                if not pdom(o, ot):
                    fails.append((q, a, b, mu, mut, p, case, o, ot))
                # auxiliary claims inside the proof
                if case in ('MR', 'AR'):
                    if not (sum(mut[1]) >= sum(mu[1]) + 1 and sum(mut[0]) >= sum(mu[0]) + 1): aux_fails += 1
                    if not (lm < p <= ltm): aux_fails += 1
                if case == 'AR':
                    j = q + 1 - p
                    if not (lm <= q - lp < p and ltp <= q - p == j - 1): aux_fails += 1
                    # second component must in fact satisfy mu- <= mut- - e_p  (the MR argument reused)
                    if not dom(mu[1], remove_box(mut[1], p)): aux_fails += 1
                    if not dom(add_box(mu[0], j), mut[0]): aux_fails += 1
                if case == 'MR':
                    if not dom(add_one(mu[0]), mut[0]): aux_fails += 1
                    if not dom(mu[1], remove_box(mut[1], p)): aux_fails += 1
    return len(P), npairs, npairs_strict, case_count, fails, aux_fails

# ---------- C3: (P1) by brute force ----------
def shape(xi, eta):
    c = Counter(xi); c.subtract(Counter(eta))
    lp = tuple(sorted([v for v in c.values() if v > 0], reverse=True))
    lm = tuple(sorted([-v for v in c.values() if v < 0], reverse=True))
    return (lp, lm)

def check_C3(q, a, b):
    """tails in Omega^a x Omega^b (a = alpha-1); adding a value u at the new x-index."""
    Omega = range(q)
    fails = 0; ntails = 0
    for xi in itertools.product(Omega, repeat=a):
        for eta in itertools.product(Omega, repeat=b):
            ntails += 1
            mu = shape(xi, eta)
            if not in_BPar(mu, q, a, b): fails += 1
            got = Counter(shape((u,) + xi, eta) for u in Omega)
            want = Counter(o for _, o in opts(mu, q))
            if got != want: fails += 1
    return ntails, fails

# ---------- C4: down-sets, second sentence, (7.1) ----------
def down_sets(P):
    """all down-sets of the poset (P, product weak dominance); P small."""
    n = len(P)
    below = [[j for j in range(n) if pdom(P[j], P[i])] for i in range(n)]
    for mask in range(1 << n):
        ok = True
        for i in range(n):
            if mask >> i & 1:
                for j in below[i]:
                    if not (mask >> j & 1): ok = False; break
                if not ok: break
        if ok:
            yield frozenset(P[i] for i in range(n) if mask >> i & 1)

def check_C4(q, alpha, beta):
    Pbig = BPar(q, alpha, beta); Psmall = BPar(q, alpha - 1, beta)
    nds = 0; fails = 0; f71_fails = 0
    for Lam in down_sets(Pbig):
        nds += 1
        F = {}
        for mu in Psmall:
            O = opts(mu, q)
            inL = [o in Lam for _, o in O]
            F[mu] = sum(inL)
            # initial segment (Lemma 7.3)
            if any(inL[i] and not inL[i-1] for i in range(1, q)): fails += 1
            # (7.1)
            lp, lm = len(mu[0]), len(mu[1])
            r = sum(1 for i in range(lm) if inL[i])
            iota = 1 if (lp + lm < q and (add_one(mu[0]), mu[1]) in Lam) else 0
            js = [j for j in range(1, lp + 1) if (add_box(mu[0], j), mu[1]) in Lam]
            j0 = min(js) if js else None
            if js and js != list(range(j0, lp + 1)): f71_fails += 1
            if j0 is not None and runder(mu[0], j0) != j0: f71_fails += 1
            if r > 0 and rbar(mu[1], r) != r: f71_fails += 1
            f71 = r + (q - lp - lm) * iota + ((lp - j0 + 1) if j0 is not None else 0)
            if f71 != F[mu]: f71_fails += 1
            # the 'in particular' formula
            if j0 is not None: phi = q - j0 + 1
            elif iota == 1: phi = q - lp
            else: phi = r
            if phi != F[mu]: f71_fails += 1
            if j0 is not None and not (r == lm and (iota == 1 or lp + lm == q)): f71_fails += 1
            if iota == 1 and r != lm: f71_fails += 1
        # order-reversing and Lambda_i down-sets
        for mu in Psmall:
            for mut in Psmall:
                if pdom(mu, mut) and F[mu] < F[mut]: fails += 1
        for i in range(q):
            Li = {mu for mu in Psmall if F[mu] > i}
            for mut in Li:
                for mu in Psmall:
                    if pdom(mu, mut) and mu not in Li: fails += 1
    return nds, fails, f71_fails

# =====================================================================
print("=== C0 ===")
tot_fail = check_C0(12)

print("=== C1 (chain + membership) and C2 (Prop. 7.4, every comparable ordered pair, every p) ===")
cells = [(q, al, be) for q in (3, 5, 7) for al in range(1, 5) for be in range(0, 5)]
# extra cells so that the cases MR and AR are exercised with long partitions (AR needs l+ + lt- >= q+1)
extra = [(7, 5, 5), (7, 6, 6), (9, 6, 6), (9, 7, 7), (9, 9, 8), (3, 9, 9), (3, 12, 10), (9, 5, 9)]
grand_pairs = 0; grand_strict = 0; grand_cases = Counter(); all_fails = []; grand_aux = 0
for (q, al, be) in cells + extra:
    t0 = time.time()
    n1, f1 = check_C1(q, al - 1, be)
    nP, npairs, nstrict, cc, fails, auxf = check_C2(q, al - 1, be)
    grand_pairs += npairs; grand_strict += nstrict; grand_cases += cc; all_fails += fails; grand_aux += auxf
    tot_fail += f1 + len(fails) + auxf
    tag = "sweep" if (q, al, be) in cells else "extra"
    print(f"[{tag}] q={q} alpha={al} beta={be}: |BPar_q(alpha-1,beta)|={nP:4d}  options={n1:5d} (C1 fails {f1})  "
          f"comparable ordered pairs={npairs:6d} (strict {nstrict:6d})  Prop7.4 fails={len(fails)}  aux fails={auxf}  "
          f"cases={dict(sorted(cc.items()))}  [{time.time()-t0:.2f}s]")
print(f"TOTAL comparable ordered pairs = {grand_pairs} (strict {grand_strict}); Prop 7.4 failures = {len(all_fails)}; "
      f"auxiliary-claim failures = {grand_aux}")
print(f"TOTAL case tallies over all (pair, p): {dict(sorted(grand_cases.items()))}")
for f in all_fails[:20]:
    print("   FAIL:", f)

print("=== C3 ((P1) by brute force on tails) ===")
for (q, al, be) in [(3,1,1),(3,2,2),(3,3,3),(3,4,4),(3,3,4),(5,1,1),(5,2,2),(5,3,2),(5,2,3),(5,3,3),(7,2,2),(7,3,2),(7,2,3)]:
    a, b = al - 1, be
    if q ** (a + b) > 30000: continue
    t0 = time.time()
    nt, f3 = check_C3(q, a, b)
    tot_fail += f3
    print(f"  q={q} alpha={al} beta={be}: tails={nt:6d} (P1) fails={f3}  [{time.time()-t0:.2f}s]")

print("=== C4 (every down-set Lambda of BPar_q(alpha,beta): F order-reversing, Lambda_i down-sets, (7.1)) ===")
for (q, al, be) in [(3,1,1),(3,2,1),(3,2,2),(3,3,2),(3,3,3),(3,4,3),(3,4,4),(5,1,1),(5,2,1),(5,2,2),(5,3,2),(5,3,3),(7,2,2),(7,3,2),(7,3,3),(9,3,3)]:
    n = len(BPar(q, al, be))
    if n > 16:
        print(f"  q={q} alpha={al} beta={be}: |BPar|={n} > 16, skipped"); continue
    t0 = time.time()
    nds, f4, f71 = check_C4(q, al, be)
    tot_fail += f4 + f71
    print(f"  q={q} alpha={al} beta={be}: |BPar_q(alpha,beta)|={n:3d} down-sets={nds:5d}  fails={f4}  (7.1)-fails={f71}  [{time.time()-t0:.2f}s]")

print(f"=== GRAND TOTAL FAILURES = {tot_fail}   wall = {time.time()-t_start:.2f}s ===")
