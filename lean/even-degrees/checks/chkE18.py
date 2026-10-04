# chkE18.py — Grepy Mandalay, 3 Oct 2026. Brute force for E18 (q_even_block_minus.md):
# Lemma 9.9 of paper v11 (the block of colour -1 at an odd prime is the odd box r = q), computed in
# the LITERAL ring R_{c,-1} = F_p[t_s]/((t_s + 1)^q) with the literal generators of (6.2):
#   pair {0, k0}: (t_{k0} - 1);  pair {i < l}, i != 0: (t_l - 1) * (t_i t_l - 1)^(q-1);
# compared with the odd-box ideal in y-coordinates, with N_q(2a) = QkEven(a-1, q+1), and with the
# colour-1 block (point t = 1) as a control. Also (a+b)^(q-1) = sum_u (-1)^u a^u b^(q-1-u) mod p.
import itertools, math, sys
import numpy as np

NCHK = 0; NFAIL = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        if NFAIL <= 30: print('FAIL', name, flush=True)

def QkEven(k, m):
    H = (m - 2) // 2; tot = 0
    for c in range(k + 2):
        rest = k + 1 - c
        for b in itertools.product(range(rest + 1), repeat=H):
            if sum(b) != rest: continue
            d = math.factorial(2 * c)
            for x in b: d *= math.factorial(x) ** 2
            tot += math.factorial(2 * k + 2) // d
    return tot

# polynomials in s_1..s_n over F_p, truncated at s_i^q (box), as dicts {exponent tuple: coef}
def pmul(a, b, p, q):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            if any(x >= q for x in e): continue
            r[e] = (r.get(e, 0) + ca * cb) % p
    return {e: c for e, c in r.items() if c}
def padd(a, b, p):
    r = dict(a)
    for e, c in b.items(): r[e] = (r.get(e, 0) + c) % p
    return {e: c for e, c in r.items() if c}
def pconst(c, n, p): return {(0,) * n: c % p} if c % p else {}
def pvar(i, n): e = [0] * n; e[i] = 1; return {tuple(e): 1}
def ppow(a, k, n, p, q):
    r = pconst(1, n, p)
    for _ in range(k): r = pmul(r, a, p, q)
    return r

def rank_mod_p(M, p):
    M = M.copy() % p; r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]: piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        nz = np.nonzero(M[:, c])[0]
        for i in nz:
            if i != r: M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows: break
    return r

def ideal_dim(gens, n, p, q):
    mons = list(itertools.product(range(q), repeat=n)); idx = {e: j for j, e in enumerate(mons)}
    rows = []
    for g in gens:
        for e in mons:
            prod = pmul(g, {e: 1}, p, q)
            if not prod: continue
            v = np.zeros(len(mons), dtype=np.int64)
            for ee, c in prod.items(): v[idx[ee]] = c
            rows.append(v)
    if not rows: return 0
    return rank_mod_p(np.array(rows), p)

def perfect_matchings(V):
    if not V: yield []; return
    a = V[0]
    for j in range(1, len(V)):
        b = V[j]; rest = V[1:j] + V[j + 1:]
        for m in perfect_matchings(rest): yield [(a, b)] + m

def literal_block(p, q, size, has0, point):
    # vertices: 0 (if has0) and 1..; variables = non-zero vertices; t_s = s_s + point
    V = list(range(size)) if has0 else list(range(1, size + 1))
    var = [v for v in V if v != 0]; n = len(var); pos = {v: i for i, v in enumerate(var)}
    def t(v): return padd(pvar(pos[v], n), pconst(point, n, p), p)
    gens = []
    for P in perfect_matchings(V):
        g = pconst(1, n, p)
        for (a, b) in P:
            a, b = min(a, b), max(a, b)
            if a == 0:
                f = padd(t(b), pconst(-1, n, p), p)
            else:
                f = pmul(padd(t(b), pconst(-1, n, p), p),
                         ppow(padd(pmul(t(a), t(b), p, q), pconst(-1, n, p), p), q - 1, n, p, q), p, q)
            g = pmul(g, f, p, q)
        gens.append(g)
    return ideal_dim(gens, n, p, q)

def ybox_block(p, q, size, has0):
    # odd box r = q: generators prod over pairs avoiding 0 of (y_i + y_l)^(q-1), in F_p[y]/(y^q)
    V = list(range(size)) if has0 else list(range(1, size + 1))
    var = [v for v in V if v != 0]; n = len(var); pos = {v: i for i, v in enumerate(var)}
    gens = []
    for P in perfect_matchings(V):
        g = pconst(1, n, p)
        for (a, b) in P:
            if min(a, b) == 0: continue
            g = pmul(g, ppow(padd(pvar(pos[a], n), pvar(pos[b], n), p), q - 1, n, p, q), p, q)
        gens.append(g)
    return ideal_dim(gens, n, p, q)

# (a+b)^(q-1) = sum_u (-1)^u a^u b^(q-1-u) mod p
for (p, v) in [(3, 1), (3, 2), (5, 1), (7, 1), (3, 3)]:
    q = p ** v
    for u in range(q):
        check(f'binom {p,v,u}', math.comb(q - 1, u) % p == (-1) ** u % p)

CTRL = {'colour1-point': 0, 'wrong-box': 0}
CELLS = [(3, 1, 2), (3, 1, 4), (3, 1, 6), (5, 1, 2), (5, 1, 4), (7, 1, 2), (7, 1, 4), (3, 2, 2), (3, 2, 4)]
for (p, v, size) in CELLS:
    q = p ** v; a = size // 2; N = QkEven(a - 1, q + 1)
    for has0 in (True, False):
        nvar = size - 1 if has0 else size
        if q ** nvar > 800: continue
        L = literal_block(p, q, size, has0, -1)
        Y = ybox_block(p, q, size, has0)
        check(f'literal=ybox {p,v,size,has0}', L == Y)
        check(f'>= N_q(2a) {p,v,size,has0}', L >= N)
        C1 = literal_block(p, q, size, has0, 1)
        if C1 != L: CTRL['colour1-point'] += 1
        if QkEven(a - 1, q) != L: CTRL['wrong-box'] += 1
        print(f'p={p} q={q} |C_-1|={size} 0in={has0}: literal={L} ybox={Y} N_q(2a)={N} colour1point={C1}', flush=True)
print('controls fired (must be >0 each):', CTRL)
check('controls', all(x > 0 for x in CTRL.values()))
print(f'checks {NCHK} failures {NFAIL}')
print('FIN-OK' if NFAIL == 0 else 'FIN-FAIL')
