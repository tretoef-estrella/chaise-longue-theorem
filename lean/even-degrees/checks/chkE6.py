# chkE6.py -- brute force for piece E6 (q_oddbox_shapes.md), paper v11 §8.1-§8.2.
# Grepy Chats, 2 Oct 2026.  Own code; mirrors the LEAN definitions (opt with L = 2h, re-sorting).
# ESTIMATE WRITTEN BEFORE RUNNING: pure Python, integers and small tuples.
#   A (identities): polynomials as dicts, r <= 13: < 1 s.
#   B (shapes/options): all tails M' in T^(m-1), r^(m-1)*r <= 5^5 = 3125, 7^4 = 2401: < 5 s.
#   C (chain): all subsets of Sh_m, |Sh_m| <= 16 -> 65536 subsets x |Sh_m| checks: < 60 s.
#   Memory: < 100 MB.  Run inside vigia.sh with the default cap (1.2 GB / 600 s).
import itertools, sys
from collections import Counter

FAILS = 0; CHECKS = 0
def check(name, ok):
    global FAILS, CHECKS
    CHECKS += 1
    if not ok: FAILS += 1
    print(('ok   ' if ok else 'FAIL ') + name); sys.stdout.flush()

# ---------------------------------------------------------------- A. identities (8.1)-(8.4)
def padd(p, q, s=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + s * v
        if r[k] == 0: del r[k]
    return r
def pmul(p, q):
    r = {}
    for (i, j), v in p.items():
        for (k, l), w in q.items():
            r[(i + k, j + l)] = r.get((i + k, j + l), 0) + v * w
    return {k: v for k, v in r.items() if v}
def Dab(q):                      # LEAN: ColOne.Dab q a b = sum_{u < q-1} (-1)^u a^u b^(q-2-u)
    return {(u, q - 2 - u): (-1) ** u for u in range(q - 1)}
def swap(p): return {(j, i): v for (i, j), v in p.items()}
A_ = {(1, 0): 1}; B_ = {(0, 1): 1}
def mono(i, j, c=1): return {(i, j): c}

def identities(r):
    D, Dm = Dab(r + 1), Dab(r)                      # D = D_r, D^- (box r)
    i81a = swap(D) == D
    i81b = swap(Dm) == {k: -v for k, v in Dm.items()}
    i82 = D == padd(mono(0, r - 1), pmul(A_, Dm), -1)
    i83a = pmul(padd(A_, B_), D) == padd(mono(r, 0), mono(0, r))
    i83b = pmul(padd(A_, B_), Dm) == padd(mono(0, r - 1), mono(r - 1, 0), -1)
    i84a = all(D.get((r - 1 - u, u), 0) == (-1) ** u for u in range(r)) and len(D) == r
    i84b = all(Dm.get((r - 2 - u, u), 0) == -(-1) ** u for u in range(r - 1)) and len(Dm) == r - 1
    return i81a, i81b, i82, i83a, i83b, i84a, i84b

for r in (3, 5, 7, 9, 11, 13):
    check('A identities (8.1)-(8.4), r=%d' % r, all(identities(r)))
# controls: for EVEN r the parity-dependent ones must fail, the others must hold
ctrl = [identities(r) for r in (2, 4, 6, 8)]
# (first run, kept as chkE6_first_run_wrong_control_expectation.log: I expected (8.3b) to hold for even r; it does
#  not -- (a+b)D^- = b^(r-1) - (-a)^(r-1), so its sign also depends on the parity. Only (8.2) is parity-free.)
check('A control: even r breaks (8.1a),(8.1b),(8.3a),(8.3b),(8.4a),(8.4b) and keeps (8.2)',
      all((not c[0]) and (not c[1]) and c[2] and (not c[3]) and (not c[4]) and (not c[5]) and (not c[6]) for c in ctrl))
# the parity-free form of (8.3): (a+b)*Dab(q) = b^(q-1) - (-a)^(q-1), every q >= 1
check('A parity-free (8.3): (a+b)*Dab q a b = b^(q-1) - (-a)^(q-1), q = 1..14',
      all(pmul(padd(A_, B_), Dab(q)) == padd(mono(0, q - 1), mono(q - 1, 0, (-1) ** (q - 1)), -1) for q in range(1, 15)))
print('   control detail (r=4):', identities(4))

# ---------------------------------------------------------------- partitions as in the LEAN files
def subE(mu, j):                 # mu - e_j (j >= 1), re-sorted, zeros dropped
    l = list(mu); l[j - 1] -= 1
    return tuple(sorted([x for x in l if x != 0], reverse=True))
def addE(mu, j):
    l = list(mu); l[j - 1] += 1
    return tuple(sorted(l, reverse=True))
def addOne(mu): return tuple(mu) + (1,)
def opt(mu, L, p):               # LEAN: ChainLemma.Partition.opt
    l = len(mu)
    if p <= l: return subE(mu, p)
    if p <= L - l: return addOne(mu)
    return addE(mu, L + 1 - p)
def optOdd(mu, d, h, p):         # the list of Lemma 8.3, p = 1..2h+1
    l = len(mu)
    if p <= l: return (opt(mu, 2 * h, p), d)
    if p == l + 1: return (mu, 1 - d)
    return (opt(mu, 2 * h, p - 1), d)
def wdom(a, b):
    sa = sb = 0
    for t in range(max(len(a), len(b))):
        sa += a[t] if t < len(a) else 0; sb += b[t] if t < len(b) else 0
        if sa > sb: return False
    return True
def partitions_le(n, h):         # all partitions with <= h parts and size <= n
    out = [()]
    def rec(pref, rem, mx):
        for x in range(min(rem, mx), 0, -1):
            q = pref + (x,); out.append(q)
            if len(q) < h: rec(q, rem - x, x)
    if h > 0: rec((), n, n)
    return out
def Par(h, n):                   # LEAN: Lifts.Par h n  (n >= 0)
    return [l for l in partitions_le(n, h) if sum(l) % 2 == n % 2]
def Sh(h, m):                    # marked part only if m >= 1
    return [(l, 0) for l in Par(h, m)] + ([(l, 1) for l in Par(h, m - 1)] if m >= 1 else [])

# ---------------------------------------------------------------- B. shapes and options (Lemma 8.1, (8.5))
def setting(h):                  # T = {0, 1..h, -1..-h}
    return [0] + [u for i in range(1, h + 1) for u in (i, -i)]
def shape(M, T):
    c = Counter(M)
    parts = sorted([c[u] - c[-u] for u in T if u != 0 and c[u] - c[-u] > 0], reverse=True)
    return (tuple(parts), c[0] % 2)

def test_B(h, m, wrong=None):
    """for every tail M' in T^(m-1): multiset {shape(t,M')} == multiset {optOdd_p} ; all in Sh_m.
       wrong = None (the statement) or a name of a deliberately wrong variant (control)."""
    T = setting(h); r = 2 * h + 1; ShM = set(Sh(h, m)); ShT = set(Sh(h, m - 1)); bad = 0; tails = 0
    for Mp in itertools.product(T, repeat=m - 1):
        tails += 1
        mu, d = shape(Mp, T)
        if (mu, d) not in ShT: bad += 1; continue
        lhs = Counter(shape((t,) + Mp, T) for t in T)
        if wrong is None:
            rhs = Counter(optOdd(mu, d, h, p) for p in range(1, r + 1))
        elif wrong == 'nomark':      # forget the zero option: (mu, d) instead of (mu, 1-d)
            rhs = Counter(optOdd(mu, d, h, p) if p != len(mu) + 1 else (mu, d) for p in range(1, r + 1))
        elif wrong == 'L=2h+1':      # one middle option too many, no zero option
            rhs = Counter((opt(mu, 2 * h + 1, p), d) for p in range(1, r + 1))
        if lhs != rhs: bad += 1
        if wrong is None and not all(s in ShM for s in lhs): bad += 1
    return bad, tails

for (h, m) in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (3, 4)]:
    bad, tails = test_B(h, m)
    check('B Lemma 8.1 (options as a multiset, all in Sh_m): h=%d m=%d, %d tails' % (h, m, tails), bad == 0)
for (h, m) in [(1, 3), (2, 3), (2, 4), (3, 3)]:
    b1, t1 = test_B(h, m, 'nomark'); b2, t2 = test_B(h, m, 'L=2h+1')
    check('B control h=%d m=%d: wrong variants fail (no mark switch: %d of %d tails; L=2h+1: %d of %d)' % (h, m, b1, t1, b2, t2),
          b1 == t1 and b2 > 0)
# the shape lies in Sh_m and |lambda| + delta has the parity of m; Sh_0 = {(empty,0)}
check('B Sh_0 = {(empty, 0)} for h = 1, 2, 3', all(Sh(h, 0) == [((), 0)] for h in (1, 2, 3)))
for (h, m) in [(1, 5), (2, 4), (3, 3)]:
    T = setting(h)
    ok = all((lambda s: len(s[0]) <= h and sum(s[0]) + s[1] <= m and (sum(s[0]) + s[1]) % 2 == m % 2)(shape(M, T))
             for M in itertools.product(T, repeat=m))
    check('B shape of every M in T^m: len <= h, |lambda|+delta <= m, same parity as m (h=%d m=%d)' % (h, m), ok)

# (8.5): F_Lambda(mu,delta) = F*_{Lambda^delta}(mu) + [mu in Lambda^{1-delta}], on random Lambda and by points
import random
random.seed(20261002)
def FLam(h, Lam, mu):            # LEAN: Fibres.FLam h Lam mu  (Lam a set of partitions)
    return sum(1 for p in range(1, 2 * h + 1) if opt(mu, 2 * h, p) in Lam)
def FOdd(h, Lam, mu, d):
    Ld = {l for (l, e) in Lam if e == d}; Lo = {l for (l, e) in Lam if e == 1 - d}
    return FLam(h, Ld, mu) + (1 if mu in Lo else 0)
for (h, m) in [(1, 4), (2, 4), (3, 3)]:
    T = setting(h); S = Sh(h, m); bad = 0; n = 0
    for trial in range(40):
        Lam = set(s for s in S if random.random() < 0.5)
        for Mp in itertools.product(T, repeat=m - 1):
            n += 1
            mu, d = shape(Mp, T)
            if sum(1 for t in T if shape((t,) + Mp, T) in Lam) != FOdd(h, Lam, mu, d): bad += 1
    check('B (8.5) on 40 random subsets Lambda of Sh_m, every tail (h=%d m=%d, %d cases)' % (h, m, n), bad == 0)

# ---------------------------------------------------------------- C. interlaced pairs and the chain (Lemma 8.3)
def is_downset_par(h, n, A):     # LEAN: Lifts.IsDownSetPar h n A
    P = Par(h, n); Ps = set(P)
    return all(a in Ps for a in A) and all(l in A for mu in A for l in P if wdom(l, mu))
def is_interlaced(h, m, Lam):
    S = set(Sh(h, m))
    if not all(s in S for s in Lam): return False
    L0 = {l for (l, e) in Lam if e == 0}; L1 = {l for (l, e) in Lam if e == 1}
    if not is_downset_par(h, m, L0): return False
    if m >= 1 and not is_downset_par(h, m - 1, L1): return False
    if m == 0 and L1: return False
    return all((subE(nu, j), 1 - d) in Lam for (nu, d) in Lam for j in range(1, len(nu) + 1))
def is_d1_only(h, m, Lam):
    L0 = {l for (l, e) in Lam if e == 0}; L1 = {l for (l, e) in Lam if e == 1}
    return is_downset_par(h, m, L0) and is_downset_par(h, m - 1, L1)
def chain_ok(h, m, Lam, order='paper'):
    """Lemma 8.3: for every (mu, d) in Sh_{m-1}, {p : optOdd_p in Lam} = {1..F_Lam(mu,d)}."""
    r = 2 * h + 1
    for (mu, d) in Sh(h, m - 1):
        if order == 'paper':
            lst = [optOdd(mu, d, h, p) for p in range(1, r + 1)]
        else:                        # control: the zero option placed LAST
            lst = [(opt(mu, 2 * h, p), d) for p in range(1, 2 * h + 1)] + [(mu, 1 - d)]
        mem = [s in Lam for s in lst]
        F = FOdd(h, Lam, mu, d)
        if sum(mem) != F: return False
        if mem != [True] * F + [False] * (r - F): return False
    return True
def all_subsets(S):
    for bits in range(1 << len(S)):
        yield frozenset(S[i] for i in range(len(S)) if bits >> i & 1)

ref = {(1, 2): 3, (1, 3): 4}     # non-empty interlaced pairs counted by fria_gate1 (r=3; 2 Oct, cold audit)
tot_pairs = 0
for (h, m) in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]:
    S = Sh(h, m)
    pairs = [L for L in all_subsets(S) if is_interlaced(h, m, L)]
    bad = sum(1 for L in pairs if not chain_ok(h, m, L))
    tot_pairs += len(pairs)
    extra = ''
    if (h, m) in ref:
        extra = '; non-empty pairs %d (cold audit: %d)' % (len(pairs) - 1, ref[(h, m)])
        check('C cross-check of the enumerator with the cold audit, h=%d m=%d' % (h, m), len(pairs) - 1 == ref[(h, m)])
    check('C Lemma 8.3 (initial segment of length F) for ALL interlaced pairs: h=%d m=%d, |Sh_m|=%d, %d pairs%s'
          % (h, m, len(S), len(pairs), extra), bad == 0)
    # (D2) is well typed: the shape (nu - e_j, 1 - delta) lies in Sh_m
    Ss = set(S)
    check('C (D2) well typed: (nu - e_j, 1-delta) in Sh_m for every (nu,delta) in Sh_m (h=%d m=%d)' % (h, m),
          all((subE(nu, j), 1 - d) in Ss for (nu, d) in S for j in range(1, len(nu) + 1)))
print('   total interlaced pairs tested (the empty one included):', tot_pairs)

# controls for C
for (h, m) in [(1, 3), (1, 4), (2, 3), (2, 4), (3, 3)]:
    S = Sh(h, m)
    d1 = [L for L in all_subsets(S) if is_d1_only(h, m, L) and not is_interlaced(h, m, L)]
    f1 = sum(1 for L in d1 if not chain_ok(h, m, L))
    pairs = [L for L in all_subsets(S) if is_interlaced(h, m, L)]
    f2 = sum(1 for L in pairs if not chain_ok(h, m, L, order='zero last'))
    check('C control h=%d m=%d: pairs of down-sets WITHOUT (D2) break the chain in %d of %d; zero option placed last breaks it in %d of %d interlaced pairs'
          % (h, m, f1, len(d1), f2, len(pairs)), f1 > 0 and f2 > 0)

# hints used in the proof: (mu + e_j) - e_j' = mu for the position j' of the raised row; (mu ⊔ 1) - e_{l+1} = mu
ok = True; n = 0
for h in (1, 2, 3, 4):
    for mu in partitions_le(9, h):
        l = len(mu)
        if subE(addOne(mu), l + 1) != mu: ok = False
        for j in range(1, l + 1):
            n += 1
            nu = addE(mu, j)
            jp = min(i for i in range(1, l + 1) if mu[i - 1] == mu[j - 1])      # first row of that length
            if subE(nu, jp) != mu: ok = False
check('hint: (mu+e_j) - e_{j_low} = mu and (mu ⊔ 1) - e_{l+1} = mu (%d cases)' % n, ok)

# (B3) directly, for every shape of Sh_{m-1} (not only shapes of tails), and Sh_m by its characterization
def in_Sh_char(h, m, s): return len(s[0]) <= h and sum(s[0]) + s[1] <= m and (sum(s[0]) + s[1]) % 2 == m % 2
for h in (1, 2, 3, 4):
    okc = all(set(Sh(h, m)) == {s for s in [(l, d) for l in partitions_le(m, h) for d in (0, 1)] if in_Sh_char(h, m, s)} for m in range(0, 9))
    check('B Sh_m = {len <= h, |lambda|+delta <= m, same parity} for m = 0..8 (h=%d)' % h, okc)
    ok3 = all(optOdd(mu, d, h, p) in set(Sh(h, m)) for m in range(1, 9) for (mu, d) in Sh(h, m - 1) for p in range(1, 2 * h + 2))
    check('B (B3): optS_p(mu,delta) in Sh_m for every (mu,delta) in Sh_{m-1}, every p, m = 1..8 (h=%d)' % h, ok3)
    # control: with the unmarked list (opt_p(mu), delta) of L = 2h+1 instead, some option leaves Sh_m when l = h
    bad3 = sum(1 for m in range(1, 9) for (mu, d) in Sh(h, m - 1) for p in range(1, 2 * h + 2) if (opt(mu, 2 * h + 1, p), d) not in set(Sh(h, m)))
    check('B control (B3): the list with L = 2h+1 and no zero option leaves Sh_m (%d options, h=%d)' % (bad3, h), bad3 > 0)
# (B5): F_Lambda(mu,delta) = #{p : optS_p in Lambda}, random Lambda, every shape with len <= h
okb5 = True; n5 = 0
for h in (1, 2, 3):
    for m in range(1, 7):
        S = Sh(h, m)
        for trial in range(30):
            Lam = set(x for x in S if random.random() < 0.5)
            for (mu, d) in Sh(h, m - 1):
                n5 += 1
                if FOdd(h, Lam, mu, d) != sum(1 for p in range(1, 2 * h + 2) if optOdd(mu, d, h, p) in Lam): okb5 = False
check('B (B5): F_Lambda(mu,delta) = #{p : optS_p(mu,delta) in Lambda} (%d cases)' % n5, okb5)
# (C1) and (C3)
okc3 = True; bad_par = 0
for h in (1, 2, 3):
    for m in range(0, 8):
        if not is_interlaced(h, m, frozenset()): okc3 = False
        if not is_interlaced(h, m, frozenset(Sh(h, m))): okc3 = False
        e = is_interlaced(h, m, frozenset([((), 0)])); o = is_interlaced(h, m, frozenset([((1,), 0), ((), 1)]))
        if m % 2 == 0 and not e: okc3 = False
        if m % 2 == 1 and not o: okc3 = False
        if m % 2 == 1 and e: bad_par += 1          # control: wrong parity must fail
        if m % 2 == 0 and o: bad_par += 1
check('C (C3): empty, Sh_m, {(empty,0)} (m even), {((1),0),(empty,1)} (m odd) are interlaced, h = 1..3, m = 0..7', okc3)
check('C control (C3): the two roots at the wrong parity are NOT interlaced (accepted wrongly: %d)' % bad_par, bad_par == 0)
print('TOTAL checks %d, failures %d' % (CHECKS, FAILS))
print('FIN-OK')
