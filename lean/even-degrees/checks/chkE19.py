# chkE19.py — Grepy Mandalay, 3 Oct 2026. Brute force for E19 (q_even_block_one.md):
# Lemma 9.10 of paper v11 (the block of colour 1 at the prime 2), computed in the LITERAL ring
# F_2[t_s]/(t_s^q - 1) = F_2[t_s]/((t_s - 1)^q), q = 2^v, with the literal generators of (6.2):
#   pair {0, k0}: t_{k0} - 1;  pair {a < b}, a != 0: (t_b - 1)*(t_a t_b - 1)^(q-1).
# Case A (0 in C_1, |C_1| = 2j+2, 2j+1 variables): dim = QkEven(j, q) and the ideal is literally
#   the ideal (psi_J) of degree q (ColUpper.IK) after the increasing relabelling.
# Case B (0 notin C_1, |C_1| = 2j+2, 2j+2 variables): theta = coefficient of t_{i1}^0 (i1 = min);
#   theta(g_P) = the case-A generator with i1 in the role of 0; dim M >= dim theta(M) = dim case A.
# Also: the colour-reduction sum, dim_{F_p} (psi_J) F_p[G] = Q_k(m) for even m (p | m).
import itertools, math, sys

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

# ---- group algebra F_p[Z/m]^n: elements as dicts {exponent tuple mod m: coef mod p} ----
def gmul(a, b, p, m):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple((x + y) % m for x, y in zip(ea, eb))
            r[e] = (r.get(e, 0) + ca * cb) % p
    return {e: c for e, c in r.items() if c}
def gadd(a, b, p):
    r = dict(a)
    for e, c in b.items(): r[e] = (r.get(e, 0) + c) % p
    return {e: c for e, c in r.items() if c}
def gconst(c, n, p): return {(0,) * n: c % p} if c % p else {}
def gvar(i, n): e = [0] * n; e[i] = 1; return {tuple(e): 1}
def gpow(a, k, n, p, m):
    r = gconst(1, n, p)
    for _ in range(k): r = gmul(r, a, p, m)
    return r
def phi(u, n, p, m):  # 1 + u + ... + u^(m-1)
    r = {}; pw = gconst(1, n, p)
    for _ in range(m):
        r = gadd(r, pw, p); pw = gmul(pw, u, p, m)
    return r

# ---- dimension of an ideal: span of all monomial shifts of the generators ----
def ideal_dim_f2(gens, n, m):
    N = m ** n
    def idx(e):
        s = 0
        for x in reversed(e): s = s * m + x
        return s
    piv = {}
    for g in gens:
        for sh in itertools.product(range(m), repeat=n):
            v = 0
            for e, c in g.items():
                if c & 1: v ^= 1 << idx(tuple((x + y) % m for x, y in zip(e, sh)))
            while v:
                h = v.bit_length() - 1
                if h in piv: v ^= piv[h]
                else: piv[h] = v; break
    return len(piv), piv

def rank_mod_p_rows(rows, p):
    piv = {}  # leading col -> row (list, normalized)
    for r in rows:
        r = dict(r)
        while r:
            h = max(r)
            if h in piv:
                c = r[h]; pr = piv[h]
                for kk, vv in pr.items():
                    r[kk] = (r.get(kk, 0) - c * vv) % p
                    if r[kk] == 0: del r[kk]
            else:
                inv = pow(r[h], p - 2, p)
                piv[h] = {kk: (vv * inv) % p for kk, vv in r.items()}
                break
    return len(piv)

def ideal_dim(gens, n, p, m):
    if p == 2: return ideal_dim_f2(gens, n, m)[0]
    def idx(e):
        s = 0
        for x in reversed(e): s = s * m + x
        return s
    rows = []
    for g in gens:
        for sh in itertools.product(range(m), repeat=n):
            r = {}
            for e, c in g.items():
                j = idx(tuple((x + y) % m for x, y in zip(e, sh)))
                r[j] = (r.get(j, 0) + c) % p
            r = {kk: vv for kk, vv in r.items() if vv}
            if r: rows.append(r)
    return rank_mod_p_rows(rows, p)

def perfect_matchings(V):
    if not V: yield []; return
    a = V[0]
    for j in range(1, len(V)):
        b = V[j]; rest = V[1:j] + V[j + 1:]
        for mm in perfect_matchings(rest): yield [(a, b)] + mm

def block_gen(P, pos, n, p, q, phi_exp=None):
    # literal (6.2) at the point 1; t_v = variable pos[v]; vertex 0 is not a variable
    g = gconst(1, n, p)
    one = gconst(1, n, p); mone = gconst(-1, n, p)
    for (a, b) in P:
        a, b = min(a, b), max(a, b)
        tb = gvar(pos[b], n)
        if a == 0:
            f = gadd(tb, mone, p)
        else:
            ta = gvar(pos[a], n)
            e = q - 1 if phi_exp is None else phi_exp
            f = gmul(gadd(tb, mone, p), gpow(gadd(gmul(ta, tb, p, q), mone, p), e, n, p, q), p, q)
        g = gmul(g, f, p, q)
    return g

def theta(g, i1, coef=0):
    # coefficient of t_{i1}^coef in g = sum_j t_{i1}^j g_j, then drop the variable i1
    r = {}
    for e, c in g.items():
        if e[i1] == coef:
            ee = e[:i1] + e[i1 + 1:]
            r[ee] = (r.get(ee, 0) + c) % 2
    return {e: c for e, c in r.items() if c}

CTRL = {'wrong-count': 0, 'theta-coef1': 0, 'phi-exp-q-2': 0}

# ---- Lemma 9.10, both cases ----
for v in (1, 2, 3):
    q = 2 ** v
    for j in range(0, 3):
        # case A: C_1 = {0, 1, ..., 2j+1}, variables 1..2j+1
        nA = 2 * j + 1
        if q ** nA > 4096: continue
        VA = list(range(0, 2 * j + 2)); posA = {x: x - 1 for x in VA if x != 0}
        gensA = [block_gen(P, posA, nA, 2, q) for P in perfect_matchings(VA)]
        dA = ideal_dim(gensA, nA, 2, q)
        N = QkEven(j, q)
        check(f'A dim=QkEven q={q} j={j}', dA == N)
        if dA != QkEven(j, 2 * q): CTRL['wrong-count'] += 1
        # case A = the literal ideal (psi_J) of degree q (ColUpper.IK) in 2j+1 variables
        def psiJ(P):
            g = gconst(1, nA, 2)
            for (a, b) in P:
                a, b = min(a, b), max(a, b)
                g = gmul(g, gadd(gvar(posA[b], nA), gconst(-1, nA, 2), 2), 2, q)
                if a != 0:
                    g = gmul(g, phi(gmul(gvar(posA[a], nA), gvar(posA[b], nA), 2, q), nA, 2, q), 2, q)
            return g
        for P in perfect_matchings(VA):
            check(f'A gP=psiJ q={q} j={j}', block_gen(P, posA, nA, 2, q) == psiJ(P))
        # control: (t_a t_b - 1)^(q-2) instead of ^(q-1) changes the dimension (q >= 4)
        if q >= 4 and j >= 1:
            gc = [block_gen(P, posA, nA, 2, q, phi_exp=q - 2) for P in perfect_matchings(VA)]
            if ideal_dim(gc, nA, 2, q) != dA: CTRL['phi-exp-q-2'] += 1
        # case B: C_1 = {1, ..., 2j+2}, all variables; i1 = 1 (position 0)
        nB = 2 * j + 2
        if q ** nB > 4096:
            print(f'q={q} j={j}: caseA dim={dA} QkEven={N}', flush=True); continue
        VB = list(range(1, 2 * j + 3)); posB = {x: x - 1 for x in VB}
        gensB = [block_gen(P, posB, nB, 2, q) for P in perfect_matchings(VB)]
        dB, pivB = ideal_dim_f2(gensB, nB, q)
        check(f'B dim=QkEven q={q} j={j}', dB == N)
        # theta(g_P) = case-A generator with vertex 1 in the role of 0 (relabel b -> b-1)
        for P in perfect_matchings(VB):
            gB = block_gen(P, posB, nB, 2, q)
            th = theta(gB, 0)
            PA = [(a - 1, b - 1) for (a, b) in P]
            check(f'B theta(gP)=caseA q={q} j={j}', th == block_gen(PA, posA, nA, 2, q))
            if theta(gB, 1) != block_gen(PA, posA, nA, 2, q): CTRL['theta-coef1'] += 1
        # theta on a basis of M: rank of the image = dim case A (injectivity on M, and theta(M) = case A ideal)
        def idx_inv(s, n):
            e = []
            for _ in range(n): e.append(s % q); s //= q
            return tuple(e)
        imgs = []
        for h, vec in pivB.items():
            el = {}
            s = vec; bit = 0
            while s:
                if s & 1: el[idx_inv(bit, nB)] = 1
                s >>= 1; bit += 1
            imgs.append(theta(el, 0))
        # rank of the images
        piv2 = {}
        def idxA(e):
            s = 0
            for x in reversed(e): s = s * q + x
            return s
        for el in imgs:
            w = 0
            for e in el: w ^= 1 << idxA(e)
            while w:
                hh = w.bit_length() - 1
                if hh in piv2: w ^= piv2[hh]
                else: piv2[hh] = w; break
        check(f'B dim theta(M)=dim M q={q} j={j}', len(piv2) == dB)
        print(f'q={q} j={j}: caseA dim={dA} caseB dim={dB} theta(M)={len(piv2)} QkEven={N}', flush=True)

# ---- the colour-reduction sum: dim_{F_p} (psi_J) F_p[G] = Q_k(m), even m, p | m ----
def psi_ideal_dim(m, k, p):
    n = 2 * k + 1; V = list(range(0, 2 * k + 2)); pos = {x: x - 1 for x in V if x != 0}
    gens = []
    for P in perfect_matchings(V):
        g = gconst(1, n, p)
        for (a, b) in P:
            a, b = min(a, b), max(a, b)
            g = gmul(g, gadd(gvar(pos[b], n), gconst(-1, n, p), p), p, m)
            if a != 0:
                g = gmul(g, phi(gmul(gvar(pos[a], n), gvar(pos[b], n), p, m), n, p, m), p, m)
        gens.append(g)
    return ideal_dim(gens, n, p, m)

for (m, k, p) in [(4, 1, 2), (4, 2, 2), (6, 1, 2), (6, 1, 3), (8, 1, 2), (10, 1, 2), (10, 1, 5),
                  (12, 1, 2), (12, 1, 3)]:
    d = psi_ideal_dim(m, k, p); Q = QkEven(k, m)
    check(f'sum m={m} k={k} p={p}', d == Q)
    print(f'm={m} k={k} p={p}: dim={d} Q_k(m)={Q}', flush=True)

print('controls fired (must be >0 each):', CTRL)
check('controls', all(x > 0 for x in CTRL.values()))
print(f'checks {NCHK} failures {NFAIL}')
print('FIN-OK' if NFAIL == 0 else 'FIN-FAIL')
