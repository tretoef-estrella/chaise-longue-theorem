#!/usr/bin/env python3
"""
sec74_prop74_random_long.py -- randomized stress test of Proposition 7.4 (section 7.4) on LONG, UNEVEN
pairs of partitions at q = 3 and q = 9 (and q = 5), far beyond the exhaustive range of
sec74_prop74_bruteforce.py.  Comparable pairs mu <= mut in BPar_q(a,b) are produced by starting from a
random mu and applying random dominance-increasing moves to BOTH components:
   * move a box from a lower row to a higher row (or to a new top-most position),
   * add one box to mu+ and one box to mu- (keeps |mu+| - |mu-|, hence the cell), respecting the caps,
   * also the 'extreme' pairs (1^k) <= (k), and hand-built AR/MR stress pairs.
Then opt_p(mu) <= opt_p(mut) is checked for every p, and the case is tallied.
"""
import random, time
from collections import Counter
random.seed(20260925)
t0 = time.time()

def dom(lam, mu):
    T = max(len(lam), len(mu)); a = b = 0
    for t in range(T):
        a += lam[t] if t < len(lam) else 0
        b += mu[t] if t < len(mu) else 0
        if a > b: return False
    return True
def pdom(x, y): return dom(x[0], y[0]) and dom(x[1], y[1])
def srt(l): return tuple(sorted([v for v in l if v > 0], reverse=True))
def remove_box(lam, p): l = list(lam); l[p-1] -= 1; return srt(l)
def add_box(lam, j): l = list(lam); l[j-1] += 1; return srt(l)
def add_one(lam): return srt(list(lam) + [1])
def opts(mu, q):
    mp, mm = mu; lp, lm = len(mp), len(mm); out = []
    for p in range(1, q+1):
        if p <= lm: out.append(('R', (mp, remove_box(mm, p))))
        elif p <= q - lp: out.append(('M', (add_one(mp), mm)))
        else: out.append(('A', (add_box(mp, q+1-p), mm)))
    return out
def in_BPar(x, q, a, b):
    lp, lm = x
    return sum(lp)-sum(lm) == a-b and sum(lp)+sum(lm) <= a+b and len(lp)+len(lm) <= q

def random_partition(n, maxlen):
    """random partition of n with at most maxlen parts (rejection on length)."""
    while True:
        cuts = sorted(random.sample(range(1, n), random.randint(0, min(n-1, maxlen-1)))) if n > 1 else []
        parts = [b - a for a, b in zip([0]+cuts, cuts+[n])]
        lam = srt(parts)
        if len(lam) <= maxlen: return lam

def random_mu(q, a, b):
    while True:
        k = random.randint(0, min(a, b))         # number of pairs
        lp_len = random.randint(1, q-1) if a-k > 0 else 0
        lp = random_partition(a-k, lp_len) if a-k > 0 else ()
        lm = random_partition(b-k, q-len(lp)) if b-k > 0 and q-len(lp) > 0 else ()
        if b-k > 0 and q-len(lp) == 0: continue
        mu = (lp, lm)
        if in_BPar(mu, q, a, b): return mu

def up_move(lam):
    """move one box from a lower row i to a higher row i' < i (or create nothing new): increases dominance."""
    lam = list(lam)
    if len(lam) < 2: return tuple(lam)
    i = random.randrange(1, len(lam)); ip = random.randrange(0, i)
    lam[i] -= 1; lam[ip] += 1
    return srt(lam)

def random_pair(q, a, b, nmoves):
    mu = random_mu(q, a, b); mut = mu
    for _ in range(nmoves):
        r = random.random()
        lp, lm = mut
        if r < 0.4:
            cand = (up_move(lp), lm)
        elif r < 0.8:
            cand = (lp, up_move(lm))
        else:
            # add one box to each component (new row or existing row), keep the cell
            def grow(l):
                if l and random.random() < 0.7:
                    j = random.randrange(len(l)); return add_box(l, j+1)
                return add_one(l)
            cand = (grow(lp), grow(lm))
        if in_BPar(cand, q, a, b) and pdom(mut, cand):
            mut = cand
    assert pdom(mu, mut)
    return mu, mut

fails = []; cases = Counter(); npairs = 0; nstrict = 0
for q, a, b, N in [(3, 20, 20, 15000), (3, 30, 12, 10000), (3, 12, 30, 10000),
                   (9, 20, 20, 15000), (9, 30, 15, 10000), (9, 15, 30, 10000), (9, 26, 26, 10000),
                   (5, 24, 20, 8000)]:
    t1 = time.time(); cc = Counter(); f = 0; ns = 0
    for _ in range(N):
        mu, mut = random_pair(q, a, b, random.randint(0, 12))
        npairs += 1
        if mu != mut: nstrict += 1; ns += 1
        O, Ot = opts(mu, q), opts(mut, q)
        for p in range(q):
            case = O[p][0] + Ot[p][0]; cc[case] += 1
            if not in_BPar(O[p][1], q, a+1, b): f += 1; fails.append(('membership', q, a, b, mu, p+1))
            if not pdom(O[p][1], Ot[p][1]): f += 1; fails.append((q, a, b, mu, mut, p+1, case, O[p][1], Ot[p][1]))
    cases += cc
    print(f"q={q} a=alpha-1={a} beta={b}: {N} random comparable pairs (strict {ns}), fails={f}, cases={dict(sorted(cc.items()))} [{time.time()-t1:.1f}s]")

# hand-built stress pairs (AR / MR with long uneven partitions), q = 3 and q = 9
hand = [
 (3, ((1,1), ()), ((4,), (1,1))),                    # AR at p=2 (j=2), MR at p=1, AA at p=3
 (3, ((5,), (1,1)), ((6,), (3,))),                   # RR, RM, AA
 (3, ((2,2), ()), ((7,), (2,1))),                    # MR at p=1, AR at p=2, AA at p=3
 (3, ((4,4), ()), ((11,), (2,1))),                   # MR, AR, AA
 (9, ((1,)*5, ()), ((10,), (1,)*5)),                 # MR at p=1..4, AR at p=5, AM p=6..8, AA p=9
 (9, ((3,)*6, (1,)), ((10,6,5), (1,1,1,1))),         # AR at p=4 (j=6), lt+ = 3 <= j-1 = 5
 (9, ((2,)*7, (1,1)), ((9,7,6), (5,3,1,1))),         # AR at p=3,4 (j=7,6)
 (9, ((5,5,5,5,5,1), (2,2,1)), ((13,12,11), (5,3,3,3,1))),  # AR at p=4,5 (j=6,5); d=10
 (9, ((1,)*8, ()), ((16,), (1,)*8)),                 # MR at p=1, AR at p=2..8, AA at p=9
 (9, ((6,6,4,4,4,4), (1,)), ((13,9,7,3), (1,1,1,1,1))),  # AR at p=4,5 (j=6,5); runder_6 = 3, lt+ = 4: tight t in [3,4) impossible
]
print("--- hand-built pairs ---")
for q, mu, mut in hand:
    a = sum(mu[0]) + 3; b = sum(mu[1]) + 3      # any cell containing both; just need same difference
    same_cell = (sum(mu[0]) - sum(mu[1]) == sum(mut[0]) - sum(mut[1]))
    caps = len(mu[0]) + len(mu[1]) <= q and len(mut[0]) + len(mut[1]) <= q
    if not (same_cell and caps and pdom(mu, mut)):
        print(f"  q={q} {mu} vs {mut}: skipped (same cell={same_cell}, caps={caps}, comparable={pdom(mu, mut)})"); continue
    O, Ot = opts(mu, q), opts(mut, q)
    res = []
    for p in range(q):
        case = O[p][0] + Ot[p][0]; ok = pdom(O[p][1], Ot[p][1]); res.append(f"p{p+1}:{case}:{'ok' if ok else 'FAIL'}")
        if not ok: fails.append((q, mu, mut, p+1, case))
    print(f"  q={q} {mu} <= {mut}: " + " ".join(res))

print(f"TOTAL random pairs = {npairs} (strict {nstrict}); case tallies = {dict(sorted(cases.items()))}")
print(f"TOTAL FAILURES = {len(fails)}  wall = {time.time()-t0:.1f}s")
for f in fails[:20]: print("  FAIL:", f)
