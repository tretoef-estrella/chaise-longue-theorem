"""P3 (Prop 5.8) slice by slice, and dim V_Lambda vs |Z_Lambda|, for all down-sets of Par_m at given (q, m).
Own implementation from the definitions of Section 5 of the paper. Usage: python3 p3_slices.py q m [maxdown]
"""
import sys, time, itertools, numpy as np
from collections import defaultdict
sys.path.insert(0, __file__.rsplit('/',1)[0])
from f3linalg import Echelon

def partitions_upto(m, h):
    """all partitions lam with |lam| <= m, |lam| = m mod 2, len <= h"""
    out = []
    def gen(rem, maxpart, cur):
        if len(cur) > h: return
        out.append(tuple(cur))
        for p in range(min(rem, maxpart), 0, -1):
            gen(rem - p, p, cur + [p])
    gen(m, m, [])
    return sorted(set(l for l in out if (m - sum(l)) % 2 == 0 and len(l) <= h))

def S(lam, t):
    return sum(lam[:t])

def preceq(lam, mu):
    T = max(len(lam), len(mu), 1)
    return all(S(lam, t) <= S(mu, t) for t in range(1, T+1))

def downsets(P):
    """all down-sets of the poset (P, preceq); P small"""
    P = list(P)
    below = {a: frozenset(b for b in P if preceq(b, a)) for a in P}
    res = set([frozenset()])
    frontier = [frozenset()]
    while frontier:
        new = []
        for D in frontier:
            for a in P:
                if a not in D and below[a] - {a} <= D:
                    E = D | {a}
                    if E not in res: res.add(E); new.append(E)
        frontier = new
    return sorted(res, key=lambda D: (len(D), sorted(D)))

def conj(lam):
    return tuple(sum(1 for p in lam if p >= c) for c in range(1, (lam[0] if lam else 0) + 1))

def options(mu, q):
    """the L = q-1 options in chain order (positions 1..L) as partitions (sorted tuples), per §5.5"""
    h = (q - 1) // 2; l = len(mu); L = q - 1
    opts = []
    for j in range(l):              # removals mu - e_j, j = 1..l
        lam = list(mu); lam[j] -= 1
        opts.append(tuple(sorted([p for p in lam if p > 0], reverse=True)))
    for _ in range(L - 2*l):        # middle: mu ⊔ 1 (exists iff l < h)
        opts.append(tuple(sorted(list(mu) + [1], reverse=True)))
    for j in range(l-1, -1, -1):    # additions mu + e_j, position L+1-j: j = l..1
        lam = list(mu); lam[j] += 1
        opts.append(tuple(sorted(lam, reverse=True)))
    assert len(opts) == L
    return opts

def F_Lambda(mu, Lam, q):
    return sum(1 for o in options(mu, q) if o in Lam)

def tight_patterns(lam, I):
    """yield (pairs, blocks) : p=(|I|-|lam|)/2 disjoint pairs, blocks B_c of size lam'_c partitioning the rest"""
    I = list(I); p = (len(I) - sum(lam)) // 2
    cols = conj(lam)
    def perfect(elems):
        if not elems: yield []; return
        a = elems[0]
        for i in range(1, len(elems)):
            b = elems[i]; rest = elems[1:i] + elems[i+1:]
            for ps in perfect(rest): yield [(a, b)] + ps
    def pairsets(elems, p):
        # choose which 2p elements are paired (the others stay for the blocks), then a perfect matching of them
        for Ssub in itertools.combinations(elems, 2*p):
            left = [e for e in elems if e not in Ssub]
            for ps in perfect(list(Ssub)): yield ps, left
    def blocksets(elems, sizes):
        if not sizes: yield []; return
        s = sizes[0]
        for B in itertools.combinations(elems, s):
            rest = [e for e in elems if e not in B]
            for bs in blocksets(rest, sizes[1:]): yield [tuple(B)] + bs
    for ps, left in pairsets(I, p):
        for bs in blocksets(left, list(cols)):
            yield ps, bs

# polynomials: dict exponent-tuple -> coeff mod 3, variables indexed 0..m-1 (index a of the paper = a-1)
def pmul(f, g, box):
    out = defaultdict(int)
    for ea, ca in f.items():
        for eb, cb in g.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            if all(x < box for x in e):
                out[e] = (out[e] + ca * cb) % 3
    return {e: c for e, c in out.items() if c}

def var(i, m, e=1):
    ex = [0]*m; ex[i] = e; return {tuple(ex): 1}

def const(m, c=1): return {tuple([0]*m): c % 3}

def padd(f, g):
    out = dict(f)
    for e, c in g.items(): out[e] = (out.get(e, 0) + c) % 3
    return {e: c for e, c in out.items() if c}

def D(a, b, m, q, box):
    """D(y_a, y_b) = sum_{u=0}^{q-2} (-1)^u y_a^u y_b^{q-2-u}"""
    f = {}
    for u in range(q - 1):
        ex = [0]*m; ex[a] += u; ex[b] += q - 2 - u
        if all(x < box for x in ex): f[tuple(ex)] = (f.get(tuple(ex), 0) + (-1)**u) % 3
    return {e: c for e, c in f.items() if c}

def vandermonde(B, m, box):
    f = const(m)
    B = sorted(B)
    for i in range(len(B)):
        for j in range(i+1, len(B)):
            f = pmul(f, padd(var(B[j], m), {tuple(x*-1 if False else x for x in e): (-c) % 3 for e, c in var(B[i], m).items()}), box)
    return f

def pattern_product(ps, bs, m, q, box):
    f = const(m)
    for (a, b) in ps: f = pmul(f, D(a, b, m, q, box), box)
    for B in bs: f = pmul(f, vandermonde(B, m, box), box)
    return f

def generators(Lam, I, m, q, box):
    gens = []
    for lam in Lam:
        for ps, bs in tight_patterns(lam, I):
            g = pattern_product(ps, bs, m, q, box)
            if g: gens.append(g)
    return gens

def monomials(m, box, d):
    """exponent tuples of total degree d in the box, ordered by y_1-degree DESC then lex"""
    out = []
    def gen(i, rem, cur):
        if i == m:
            if rem == 0: out.append(tuple(cur))
            return
        for e in range(min(rem, box-1), -1, -1):
            gen(i+1, rem-e, cur+[e])
    gen(0, d, [])
    out.sort(key=lambda e: (-e[0],) + tuple(-x for x in e[1:]))
    return out

def ideal_by_degree(gens, m, q, box):
    """returns dict d -> (cols list, Echelon) for the ideal generated by homogeneous gens in C_m"""
    maxdeg = m * (box - 1)
    bydeg = defaultdict(list)
    for g in gens:
        d = sum(next(iter(g)))
        bydeg[d].append(g)
    res = {}
    prevE, prevcols = None, None
    for d in range(0, maxdeg + 1):
        cols = monomials(m, box, d); idx = {e: j for j, e in enumerate(cols)}
        E = Echelon(len(cols))
        rows = []
        for g in bydeg.get(d, []):
            v = np.zeros(len(cols), dtype=np.int8)
            for e, c in g.items(): v[idx[e]] = c
            rows.append(v)
        if prevE is not None and prevE.rank():
            for r in prevE.rows:
                nz = np.flatnonzero(r)
                for i in range(m):
                    v = np.zeros(len(cols), dtype=np.int8); any_ = False
                    for j in nz:
                        e = list(prevcols[j]); e[i] += 1
                        if e[i] < box: v[idx[tuple(e)]] = r[j]; any_ = True
                    if any_: rows.append(v)
        if rows:
            R = np.stack(rows)
            for s in range(0, len(R), 2000): E.add_many(R[s:s+2000])
        res[d] = (cols, E)
        prevE, prevcols = E, cols
    return res

def slices(ideal, m, box):
    """W_j in each degree e of C_{m-1}: dict (j, e) -> Echelon over monomials of C_{m-1} degree e (vars 1..m-1)"""
    W = {}
    for d, (cols, E) in ideal.items():
        for r, p in zip(E.rows, E.pivots):
            j = cols[p][0]                      # y_1-degree of pivot
            e = d - j
            key = (j, e)
            if key not in W:
                subcols = monomials(m - 1, box, e)
                W[key] = (subcols, {t: i for i, t in enumerate(subcols)}, Echelon(len(subcols)))
            subcols, sidx, EW = W[key]
            v = np.zeros(len(subcols), dtype=np.int8)
            for jj in np.flatnonzero(r):
                ex = cols[jj]
                if ex[0] == j: v[sidx[ex[1:]]] = r[jj]
            EW.add(v)
    return W

def member(W, j, e, g, m, box):
    key = (j, e)
    if key not in W: return False
    subcols, sidx, EW = W[key]
    v = np.zeros(len(subcols), dtype=np.int8)
    for ex, c in g.items(): v[sidx[ex]] = c
    return EW.contains(v)

def count_Z(Lam, m, q):
    """|Z_Lambda| by brute force over T^m, T = F_q^* as classes {u,-u}: values 1..h and -1..-h"""
    h = (q - 1) // 2
    vals = list(range(1, h+1)) + list(range(-h, 0))
    cnt = 0
    for M in itertools.product(vals, repeat=m):
        res = []
        for u in range(1, h+1):
            a = M.count(u); b = M.count(-u)
            if a != b: res.append(abs(a - b))
        lam = tuple(sorted(res, reverse=True))
        if lam in Lam: cnt += 1
    return cnt

def main(q, m, maxdown=None):
    t0 = time.time()
    h = (q - 1) // 2; box = q - 1
    Pm = partitions_upto(m, h); Pm1 = partitions_upto(m - 1, h)
    Ds = downsets(Pm)
    if maxdown: Ds = Ds[:maxdown]
    print(f"(q,m)=({q},{m}) h={h}: Par_m={Pm} ; Par_(m-1)={Pm1} ; {len(Ds)} down-sets")
    fails = 0; neg_fires = 0; dimeq = 0; tests = 0
    for Lam in Ds:
        Lam = set(Lam)
        gens = generators(Lam, list(range(m)), m, q, box)
        ideal = ideal_by_degree(gens, m, q, box)
        dimV = sum(E.rank() for _, E in ideal.values())
        Z = count_Z(Lam, m, q)
        W = slices(ideal, m, box)
        # layers
        Lam_i = {i: set(mu for mu in Pm1 if F_Lambda(mu, Lam, q) > i) for i in range(q - 1)}
        # check layers are down-sets of Par_{m-1}
        for i, Li in Lam_i.items():
            for mu in Li:
                for nu in Pm1:
                    if preceq(nu, mu) and nu not in Li: print("  LAYER NOT DOWN-SET", Lam, i, mu, nu); fails += 1
        # P3: generators of V_{Lam_i} on indices 1..m-1 (variables of C_{m-1}) in W_{q-2-i}
        thisfail = 0; thisneg = 0
        for i in range(q - 1):
            gi = generators(Lam_i[i], list(range(m - 1)), m - 1, q, box)
            for g in gi:
                e = sum(next(iter(g))); tests += 1
                if not member(W, q - 2 - i, e, g, m, box):
                    thisfail += 1
                if q - 3 - i >= 0 and not member(W, q - 3 - i, e, g, m, box):
                    thisneg += 1
        fails += thisfail; neg_fires += thisneg
        if dimV == Z: dimeq += 1
        print(f"  Lambda={sorted(Lam)}: #gens={len(gens)} dimV={dimV} |Z|={Z} {'EQ' if dimV==Z else ('GE' if dimV>Z else '**LT**')} ; P3 failures={thisfail} ; tighter-slice failures (neg control)={thisneg} ; layers sizes={[len(Lam_i[i]) for i in range(q-1)]}")
    print(f"SUMMARY (q,m)=({q},{m}): P3 membership tests={tests}, failures={fails}, negative-control firings={neg_fires}, down-sets with dimV==|Z|: {dimeq}/{len(Ds)} ; {time.time()-t0:.1f}s")

if __name__ == '__main__':
    q, m = int(sys.argv[1]), int(sys.argv[2])
    md = int(sys.argv[3]) if len(sys.argv) > 3 else None
    main(q, m, md)
