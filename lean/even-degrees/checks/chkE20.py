# chkE20.py — Grepy Mandalay, 3 Oct 2026. Brute force for E20 (q_even_assembly.md):
# (1) Main Theorem' for even m: dim_{F_p} (psi_J) F_p[G] = QkEven(k, m) for every prime p (dividing m
#     or not), and dim of the quotient = m^(2k+1) - QkEven(k, m).
# (2) the unified count Q(m, k) = #{g in {1..m-1}^(2k+2) admitting a perfect matching J with
#     g_{J x} = -g_x mod m}: equals QkEven for even m and the odd-m count for odd m (cells m = 3, 5, 7).
# (3) Corollary 9.12 (ii): over F_2, for q = 2, 4: dim I^bal_a = N_bal(a, q), dim I^ph_a = N_ph(a, q),
#     I^bal_a = (prod_i (x_i - z_sigma(i))^(q-1)) in F_2[x, z]/(x^q, z^q).
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

def Qunified(m, k):
    # tuples in {1..m-1}^n (n = 2k+2) whose multiset pairs a with -a mod m (m/2 with itself, even count)
    n = 2 * k + 2; tot = 0
    for g in itertools.product(range(1, m), repeat=n):
        cnt = [0] * m
        for x in g: cnt[x] += 1
        ok = True
        for a in range(1, m):
            b = (-a) % m
            if a == b:
                if cnt[a] % 2: ok = False; break
            elif cnt[a] != cnt[b]: ok = False; break
        if ok: tot += 1
    return tot

def Qk_odd(k, m):  # DS count for odd m: fibre of closed tuples on m-1 points, no fixed point
    return Qunified(m, k)

# ---- group algebra F_p[Z/m]^n ----
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
def phi(u, n, p, m):
    r = {}; pw = gconst(1, n, p)
    for _ in range(m):
        r = gadd(r, pw, p); pw = gmul(pw, u, p, m)
    return r

def rank_rows(rows, p):
    piv = {}
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

def perfect_matchings(V):
    if not V: yield []; return
    a = V[0]
    for j in range(1, len(V)):
        b = V[j]; rest = V[1:j] + V[j + 1:]
        for mm in perfect_matchings(rest): yield [(a, b)] + mm

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
    return rank_rows(rows, p)

CTRL = {'odd-formula-at-even-m': 0, 'Ibal-exp-q-2': 0, 'Nbal-wrong-q': 0}

# (2) unified count
for (m, k) in [(4, 1), (6, 1), (8, 1), (4, 2), (3, 1), (5, 1), (7, 1), (9, 1), (3, 2)]:
    Q = Qunified(m, k)
    if m % 2 == 0:
        check(f'unified=QkEven m={m} k={k}', Q == QkEven(k, m))
    print(f'Q({m},{k}) = {Q}', flush=True)

# (1) Main Theorem' for even m at every prime
for (m, k, primes) in [(4, 1, [2, 3, 5]), (4, 2, [2, 3]), (6, 1, [2, 3, 5]), (8, 1, [2, 3]),
                       (10, 1, [2, 5, 3]), (12, 1, [2, 3])]:
    Q = QkEven(k, m)
    for p in primes:
        d = psi_ideal_dim(m, k, p)
        check(f'dim m={m} k={k} p={p}', d == Q)
        check(f'quot m={m} k={k} p={p}', m ** (2 * k + 1) - d == m ** (2 * k + 1) - Q)
        print(f'm={m} k={k} p={p}: dim={d} QkEven={Q} quotient={m**(2*k+1)-d}', flush=True)
    # control: a wrong count (the odd-m formula evaluated at m-1 and m+1) must differ
    if Q != Qunified(m - 1, k) and Q != Qunified(m + 1, k): CTRL['odd-formula-at-even-m'] += 1

# (3) Corollary 9.12 (ii): bipartite ideals over F_2 at q = 2, 4
def cnt(t, u): return sum(1 for x in t if x == u)
def Nbal(a, q):
    return sum(1 for X in itertools.product(range(q), repeat=a) for Y in itertools.product(range(q), repeat=a)
               if all(cnt(X, u) == cnt(Y, u) for u in range(q)))
def Nph(a, q):
    return sum(1 for X in itertools.product(range(q), repeat=a + 1) for Y in itertools.product(range(q), repeat=a)
               if all(cnt(Y, u) <= cnt(X, u) for u in range(q)))

def tmul(a, b, q):  # truncated polynomial ring F_2[vars]/(v^q), dict exps -> coef mod 2
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            if max(e, default=0) >= q: continue
            r[e] = (r.get(e, 0) + ca * cb) % 2
    return {e: c for e, c in r.items() if c}
def tpow(a, k, nv, q):
    r = {(0,) * nv: 1}
    for _ in range(k): r = tmul(r, a, q)
    return r
def lin(i, j, nv):  # x_i - z_j = x_i + z_j over F_2 (variables x_0..x_{a-1}, z_0..z_{b-1})
    e1 = [0] * nv; e1[i] = 1; e2 = [0] * nv; e2[j] = 1
    return {tuple(e1): 1, tuple(e2): 1}
def tideal_dim(gens, nv, q):
    mons = list(itertools.product(range(q), repeat=nv))
    index = {e: i for i, e in enumerate(mons)}
    piv = {}
    for g in gens:
        for sh in mons:
            v = 0
            for e, c in g.items():
                ee = tuple(x + y for x, y in zip(e, sh))
                if max(ee, default=0) >= q: continue
                v ^= 1 << index[ee]
            while v:
                h = v.bit_length() - 1
                if h in piv: v ^= piv[h]
                else: piv[h] = v; break
    return len(piv)

def Ibal_dim(a, q, e=None):
    nv = 2 * a; ex = q - 1 if e is None else e
    gens = []
    for s in itertools.permutations(range(a)):
        g = {(0,) * nv: 1}
        for i in range(a): g = tmul(g, tpow(lin(i, a + s[i], nv), ex, nv, q), q)
        gens.append(g)
    return tideal_dim(gens, nv, q)
def Iph_dim(a, q):
    nv = 2 * a + 1; gens = []
    for i0 in range(a + 1):
        others = [i for i in range(a + 1) if i != i0]
        for s in itertools.permutations(range(a)):
            g = {(0,) * nv: 1}
            for t, i in enumerate(others): g = tmul(g, tpow(lin(i, a + 1 + s[t], nv), q - 1, nv, q), q)
            gens.append(g)
    return tideal_dim(gens, nv, q)

for q in (2, 4):
    for a in (0, 1, 2, 3):
        if q ** (2 * a + 1) > 20000: continue
        if q ** (2 * a) <= 20000:
            db = Ibal_dim(a, q); nb = Nbal(a, q)
            check(f'Ibal q={q} a={a}', db == nb)
            if nb != Nbal(a, q + 1): CTRL['Nbal-wrong-q'] += 1
            if q == 4 and a >= 1 and Ibal_dim(a, q, e=q - 2) != db: CTRL['Ibal-exp-q-2'] += 1
            print(f'q={q} a={a}: dim Ibal={db} Nbal={nb}', flush=True)
        dp = Iph_dim(a, q); npp = Nph(a, q)
        check(f'Iph q={q} a={a}', dp == npp)
        check(f'Nph=Nbal(a+1) q={q} a={a}', npp == Nbal(a + 1, q))
        print(f'q={q} a={a}: dim Iph={dp} Nph={npp}', flush=True)

print('controls fired (must be >0 each):', CTRL)
check('controls', all(x > 0 for x in CTRL.values()))
print(f'checks {NCHK} failures {NFAIL}')
print('FIN-OK' if NFAIL == 0 else 'FIN-FAIL')
