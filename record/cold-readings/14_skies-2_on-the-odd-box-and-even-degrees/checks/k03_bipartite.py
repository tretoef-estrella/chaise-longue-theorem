# k03_bipartite.py -- Grepy Skies 2. Theorem 7.6 of the paper (bipartite down-set theorem) at an EVEN box q,
# built from the definitions of the paper's section 7.2:
#   BPar_q(al,be), product weak dominance, tight patterns  prod (x_i - z_l)^{q-1} * prod Delta(x-blocks) * prod Delta(z-blocks),
#   V_Lambda in F_p[x_1..x_al, z_1..z_be]/(x^q, z^q),  Z_Lambda in Omega^al x Omega^be, |Omega| = q.
# Checked: dim V_Lambda >= |Z_Lambda| for every down-set Lambda (roots AND non-roots).
# usage: python3 k03_bipartite.py q al be p [maxsets]
import sys, itertools, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import *
from math import comb

q = int(sys.argv[1]); al = int(sys.argv[2]); be = int(sys.argv[3]); p = int(sys.argv[4])
maxsets = int(sys.argv[5]) if len(sys.argv) > 5 else 80
n = al + be
t0 = time.time()

def allparts(s):
    return list(partitions(s, s if s else 0)) if s else [()]

BP = []
for sm in range(0, be + 1):
    sp = sm + al - be
    if sp < 0 or sp + sm > al + be: continue
    for lp in allparts(sp):
        for lm in allparts(sm):
            if len(lp) + len(lm) <= q: BP.append((lp, lm))

def leq(a, b): return wleq(a[0], b[0]) and wleq(a[1], b[1])

def shape(xi, eta):
    cx = {}; cy = {}
    for v in xi: cx[v] = cx.get(v, 0) + 1
    for v in eta: cy[v] = cy.get(v, 0) + 1
    pl = []; mi = []
    for u in range(q):
        d = cx.get(u, 0) - cy.get(u, 0)
        if d > 0: pl.append(d)
        elif d < 0: mi.append(-d)
    return (tuple(sorted(pl, reverse=True)), tuple(sorted(mi, reverse=True)))

cnt = {}
for xi in itertools.product(range(q), repeat=al):
    for eta in itertools.product(range(q), repeat=be):
        s = shape(xi, eta)
        cnt[s] = cnt.get(s, 0) + 1
assert set(cnt) <= set(BP), "a point has a shape outside BPar"

def xzpow(i, l):
    """(x_i - z_l)^{q-1} over Z, variables i (x) and al+l (z)."""
    c = {}
    for u in range(q):
        k = [0] * n; k[i] = u; k[al + l] = q - 1 - u
        c[tuple(k)] = comb(q - 1, u) * (-1) ** (q - 1 - u)
    return c

def partial_matchings(A, B, s):
    for As in itertools.combinations(A, s):
        for Bs in itertools.permutations(B, s):
            yield tuple(zip(As, Bs)), [a for a in A if a not in As], [b for b in B if b not in Bs]

_pc = {}
def products(lam):
    if lam in _pc: return _pc[lam]
    lp, lm = lam
    s = al - sum(lp)
    assert s == be - sum(lm) and s >= 0
    seen = set(); out = []
    for P, restA, restB in partial_matchings(list(range(al)), list(range(be)), s):
        f0 = one(n)
        for (i, l) in P: f0 = pmul(f0, xzpow(i, l), q)
        for ba in block_splits(restA, conj(lp)):
            f1 = f0
            for blk in ba: f1 = pmul(f1, vdm(n, blk, q), q)
            if not f1: continue
            for bb in block_splits(restB, conj(lm)):
                f = f1
                for blk in bb: f = pmul(f, vdm(n, [al + b for b in blk], q), q)
                key = normal(f)
                if key is None or key in seen: continue
                seen.add(key); out.append(f)
    _pc[lam] = out
    return out

def is_down(L):
    return all((b in L) for a in L for b in BP if leq(b, a))

if len(BP) <= 14:
    downs = [L for L in all_subsets(BP) if L and is_down(L)]
else:
    downs = []
if not downs or len(downs) > maxsets:
    # principal down-sets, unions of two of them, and the full set
    prin = [frozenset(b for b in BP if leq(b, a)) for a in BP]
    cand = set(prin)
    for a, b in itertools.combinations(prin, 2): cand.add(a | b)
    cand.add(frozenset(BP))
    downs = sorted(cand, key=lambda L: (len(L), sorted(L)))[:maxsets]
    note = "(principal down-sets, unions of two, full set; truncated to %d)" % maxsets
else:
    note = "(ALL non-empty down-sets)"

def nm(s): return "(%s|%s)" % (",".join(map(str, s[0])), ",".join(map(str, s[1])))
binom_ok = all(comb(q - 1, t) % p for t in range(q))
print("q=%d (alpha,beta)=(%d,%d) p=%d: |BPar|=%d, down-sets tested %d %s; hypothesis C(q-1,t)!=0 mod p for all t: %s"
      % (q, al, be, p, len(BP), len(downs), note, binom_ok))
lt = eq = gt = 0; bad = []
for L in downs:
    z = sum(cnt.get(s, 0) for s in L)
    gens = []
    for s in sorted(L): gens.extend(products(s))
    d = idim(ideal(gens, n, q, p))
    if d < z: lt += 1; bad.append((" ".join(nm(s) for s in sorted(L)), d, z))
    elif d == z: eq += 1
    else: gt += 1
print("   dim<|Z|: %d   dim=|Z|: %d   dim>|Z|: %d   [%.1fs]" % (lt, eq, gt, time.time() - t0))
for b in bad[:6]: print("     dim<|Z|: {%s} dim=%d |Z|=%d" % b)
# roots
if al == be:
    root = frozenset([((), ())])
    N = sum(cnt.get(s, 0) for s in root)
    d = idim(ideal(products(((), ())), n, q, p))
    print("   root balanced a=%d: dim I^bal = %d, N_bal(a,q) = %d" % (al, d, N))
if al == be + 1:
    root = frozenset([((1,), ())])
    N = sum(cnt.get(s, 0) for s in root)
    d = idim(ideal(products(((1,), ())), n, q, p))
    print("   root phantom a=%d: dim I^ph = %d, N_ph(a,q) = %d" % (be, d, N))
