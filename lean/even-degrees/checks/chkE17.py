# chkE17.py — Grepy Mandalay, 3 Oct 2026. Brute force for E17 (q_even_count_colours.md):
# Lemma 9.6 of paper v11 (the count factors over the blocks SInv (+) R, the index 0 a coordinate).
# Pure Python. Model: the colours mu_r = Z/r (additive; "1" = 0, inverse = negation),
# Omega_q = Z/q (additive; "1" = 0, inverse = negation), T_m = (Z/q x Z/r) minus (0, 0),
# neg (w, z) = (-w, -z). A tuple is closed if cnt(u) = cnt(neg u) for every u and cnt(u) is even
# for every fixed point u.
import itertools, math, sys
from collections import Counter

NCHK = 0; NFAIL = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        if NFAIL <= 30: print('FAIL', name, flush=True)

def closed(t, neg):
    C = Counter(t)
    for u, n in C.items():
        if C.get(neg(u), 0) != n: return False
        if neg(u) == u and n % 2: return False
    return True

def QkEven(k, m):
    # EvenCount.QkEven (Defs.lean): sum over c in range(k+2), b : Fin((m-2)/2) -> range(2k+3),
    # 2c + 2 sum b = 2k+2, of (2k+2)! / ((2c)! prod b!^2)
    H = (m - 2) // 2; tot = 0
    for c in range(k + 2):
        rest = k + 1 - c
        if rest < 0: continue
        for b in itertools.product(range(rest + 1), repeat=H):
            if sum(b) != rest: continue
            d = math.factorial(2 * c)
            for x in b: d *= math.factorial(x) ** 2
            tot += math.factorial(2 * k + 2) // d
    return tot

def I0count(n, h):
    # (n)! [x^n] I_0(2x)^h : tuples of length n over {1..h} x {+-1} closed (no fixed point)
    if n % 2: return 0
    tot = 0
    for b in itertools.product(range(n // 2 + 1), repeat=h):
        if 2 * sum(b) != n: continue
        d = 1
        for x in b: d *= math.factorial(x) ** 2
        tot += math.factorial(n) // d
    return tot

def blockS(a, q, one):
    # tuples of length a over Z/q (minus {0} if one), closed under negation
    vals = [w for w in range(q) if not (one and w == 0)]
    neg = lambda w: (-w) % q
    return sum(1 for t in itertools.product(vals, repeat=a) if closed(t, neg))

def Nbal(a, q):
    return sum(1 for x in itertools.product(range(q), repeat=a)
               for y in itertools.product(range(q), repeat=a) if Counter(x) == Counter(y))

CTRL = Counter()
def run(p, v, r, k, sumtarget):
    q = p ** v; m = q * r; n = 2 * k + 2
    T = [(w, z) for w in range(q) for z in range(r) if (w, z) != (0, 0)]
    neg = lambda u: ((-u[0]) % q, (-u[1]) % r)
    fixed = [u for u in T if neg(u) == u]
    check(f'fixedpts {p,v,r}', len(fixed) == (1 if m % 2 == 0 else 0))
    check(f'card {p,v,r}', len(T) == m - 1)
    SInv = [z for z in range(r) if (2 * z) % r == 0]
    check(f'SInv shape {p,v,r}', SInv == ([0, r // 2] if r % 2 == 0 else [0]))
    R = [z for z in range(r) if z not in SInv and z < (-z) % r]
    # direct: closed tuples bucketed by colours
    direct = Counter(); total = 0; bad0 = 0
    for g in itertools.product(T, repeat=n):
        if not closed(g, neg): continue
        total += 1
        col = tuple(u[1] for u in g)
        if (sum(col)) % r != 0: bad0 += 1
        direct[col[1:]] += 1
    check(f'colour 0 determined {p,v,r,k}', bad0 == 0)
    if m % 2 == 0:
        check(f'total=QkEven {p,v,r,k}', total == QkEven(k, m))
    check(f'total=target {p,v,r,k}', total == sumtarget)
    S = 0; Sc1 = 0; Sc2 = 0; Sc3 = 0
    for c in itertools.product(range(r), repeat=n - 1):
        c0 = (-sum(c)) % r; ce = (c0,) + c
        cls = {z: sum(1 for x in ce if x == z) for z in range(r)}
        comp = all(cls[z] % 2 == 0 for z in SInv) and all(cls[z] == cls[(-z) % r] for z in R)
        if comp:
            prodS = 1
            for z in SInv:
                a = cls[z]; val = blockS(a, q, z == 0); prodS *= val
                # closed forms (C2)
                if z == 0 and p != 2:
                    check(f'N1 odd p {p,v,r,a}', val == I0count(a, (q - 1) // 2))
                if z == 0 and p == 2:
                    check(f'N1 p=2 {p,v,r,a}', val == (1 if a == 0 else QkEven(a // 2 - 1, q)))
                if z != 0:
                    check(f'N-1 {p,v,r,a}', val == (1 if a == 0 else QkEven(a // 2 - 1, q + 1)))
            prodR = 1
            for z in R: prodR *= Nbal(cls[z], q)
            f = prodS * prodR
            # controls
            c1 = prodR * (blockS(cls[0], q, True))            # drop the -1 block
            c2 = prodS * math.prod(Nbal(max(cls[z] - (1 if ce[0] in (z, (-z) % r) else 0), 0), q) for z in R)  # treat index 0 as a phantom
            c3 = prodR * math.prod(blockS(cls[z], q, True) for z in SInv)  # -1 block over Z/q minus 0
            Sc1 += c1; Sc2 += c2; Sc3 += c3
        else:
            f = 0
        check(f'factor {p,v,r,k,c}', direct[c] == f)
        S += f
    check(f'sum {p,v,r,k}', S == total)
    if r % 2 == 0:
        CTRL['drop-1'] += (Sc1 != total); CTRL['phantom0'] += (Sc2 != total); CTRL['minus-1 over Z/q*'] += (Sc3 != total)
    else:
        CTRL['phantom0'] += (Sc2 != total)
    print(f'cell p={p} v={v} r={r} k={k} m={m}: total={total} QkEven={QkEven(k, m) if m % 2 == 0 else "-"}', flush=True)

# (p, v, r, k, expected total)
CELLS = [(2, 1, 3, 1, None), (2, 1, 3, 2, 1001), (2, 2, 3, 1, None), (2, 1, 5, 1, None), (2, 3, 3, 1, None),
         (3, 1, 2, 1, None), (3, 1, 2, 2, 1001), (3, 1, 4, 1, None), (5, 1, 2, 1, None), (5, 1, 4, 1, None),
         (3, 2, 2, 1, None), (3, 1, 2, 3, 18733),
         (3, 1, 5, 1, None), (5, 1, 3, 1, None)]
for (p, v, r, k, tgt) in CELLS:
    q = p ** v; m = q * r
    if tgt is None:  # k = 1: Q_1(m) = 3m^2 - 9m + 7 for every m (paper v11 §9.1 and §1.2)
        assert k == 1
        tgt = 3 * m * m - 9 * m + (7 if m % 2 == 0 else 6)  # delta_m = 1 for even m, 0 for odd m
    run(p, v, r, k, tgt)
print('controls fired (must be >0 each):', dict(CTRL))
check('controls', all(x > 0 for x in CTRL.values()))
print(f'checks {NCHK} failures {NFAIL}')
print('FIN-OK' if NFAIL == 0 else 'FIN-FAIL')
