# chkE15.py — Grepy Mandalay, 3 Oct 2026. Brute force for E15 (q_oddbox_equality.md):
# (Q is proxied by the prime 32003.) Corollary 8.13 of paper v11 (equality at the odd box r = 2h+1) by the route with NO duality:
#  (a) dim_F (D_J : J) C_{2k+1} = N_r(2k+2) over F_2, F_3, F_5, F_7 and over Q (proxy: p = 1000003);
#  (b) dim_F M = N_r(2k+2), M := Σ_P D_P C_N, N = 2k+2 (all perfect matchings of N variables);
#  (c) the ring step: dim C_N/∩_P I_P C_N >= dim M (the pairing step) and = N_r(N) here;
#  (d) the θ step: [x_0^{r-1}] D(x_0, y) = 1 (r odd), so θ(D_P g) = D_J g;
#  (e) |Γ| = N_r(N) for T = {-h..h} (tuples that split into pairs {u, -u}; zeros free in pairs).
# D(a,b) = Σ_{u=0}^{r-1} (-1)^u a^u b^{r-1-u}; box x_i^r = 0.
import itertools, math
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

def Nr(r, n):  # n-tuples in T (|T| = r, one fixed point) with u, -u equally often (zeros free)
    h = (r - 1) // 2; tot = 0
    for t in itertools.product(range(-h, h + 1), repeat=n):
        if all(t.count(u) == t.count(-u) for u in range(1, h + 1)): tot += 1
    return tot

def Gamma(r, n):  # tuples that split into pairs {u, -u} (0 paired with 0)
    h = (r - 1) // 2; tot = 0
    for t in itertools.product(range(-h, h + 1), repeat=n):
        if t.count(0) % 2 == 0 and all(t.count(u) == t.count(-u) for u in range(1, h + 1)): tot += 1
    return tot

def poly_D(a, b, nv, r, coefsign=True, deg=None):
    # D(x_a, x_b) as dict {exp tuple: int}, deg r-1 (or deg for the control)
    d = r - 1 if deg is None else deg
    res = {}
    for u in range(d + 1):
        e = [0] * nv
        if a == b: continue
        e[a] += u; e[b] += d - u
        if max(e) >= r: continue
        res[tuple(e)] = res.get(tuple(e), 0) + (-1) ** u
    return {e: c for e, c in res.items() if c}

def pmul(f, g, r):
    res = {}
    for e1, c1 in f.items():
        for e2, c2 in g.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            if max(e, default=0) >= r: continue
            res[e] = res.get(e, 0) + c1 * c2
    return {e: c for e, c in res.items() if c}

def matchings(V):
    if not V: yield []; return
    a = V[0]
    for j in range(1, len(V)):
        rest = V[1:j] + V[j + 1:]
        for m in matchings(rest): yield [(a, V[j])] + m

def rref_small(M, p):
    M = M % p; rows, cols = M.shape; r = 0; piv = []
    for c in range(cols):
        if r == rows: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        if i != r: M[[r, i]] = M[[i, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        for j in np.nonzero(M[:, c])[0]:
            if j != r: M[j] = (M[j] - M[j, c] * M[r]) % p
        piv.append(c); r += 1
    return M[:r], piv

def rank_mod_p(rowgen, ncols, p, chunk=3000):
    assert p < 40000
    B = np.zeros((0, ncols), dtype=np.int64); piv = []
    def absorb(C):
        nonlocal B, piv
        if B.shape[0]:
            C = (C - (C[:, piv] @ B) % p) % p
        C = C[np.any(C != 0, axis=1)]
        if C.shape[0] == 0: return
        R, rp = rref_small(C, p)
        if B.shape[0]:
            B = (B - (B[:, rp] @ R) % p) % p
        B = np.vstack([B, R]); piv = piv + rp
    buf = []
    for row in rowgen:
        buf.append(row)
        if len(buf) >= chunk:
            absorb(np.array(buf, dtype=np.int64)); buf = []
    if buf: absorb(np.array(buf, dtype=np.int64))
    return B.shape[0]

def ideal_rows(gens, nv, r):
    mons = list(itertools.product(range(r), repeat=nv))
    idx = {e: i for i, e in enumerate(mons)}
    for g in gens:
        for sh in mons:
            row = [0] * len(mons); nz = False
            for e, c in g.items():
                ee = tuple(x + y for x, y in zip(e, sh))
                if max(ee, default=0) >= r: continue
                row[idx[ee]] += c; nz = True
            if nz: yield row

def dim_ideal(gens, nv, r, p):
    return rank_mod_p(ideal_rows(gens, nv, r), r ** nv, p)

def DJ_gens(k, r, deg=None):  # (D_J) in C_{2k+1}: vertex 0 not a variable; variables 1..2k+1 -> 0..2k
    nv = 2 * k + 1; gens = []
    for P in matchings(list(range(2 * k + 2))):
        g = {(0,) * nv: 1}
        for (a, b) in P:
            if a == 0: continue
            g = pmul(g, poly_D(a - 1, b - 1, nv, r, deg=deg), r)
        gens.append(g)
    return gens, nv

def M_gens(k, r):  # Σ_P D_P in C_N, N = 2k+2 variables
    nv = 2 * k + 2; gens = []
    for P in matchings(list(range(nv))):
        g = {(0,) * nv: 1}
        for (a, b) in P: g = pmul(g, poly_D(a, b, nv, r), r)
        gens.append(g)
    return gens, nv

def inter_dim(k, r, p):
    # dim of ∩_P I_P C_N, I_P = (x_a + x_b); computed as dim C - dim of the sum of annihilator-free
    # complement: ∩ of subspaces via rank: dim(∩ V_i) = via kernel of stacked complement maps.
    nv = 2 * k + 2; n = r ** nv
    mons = list(itertools.product(range(r), repeat=nv)); idx = {e: i for i, e in enumerate(mons)}
    # each I_P C is the span of (x_a+x_b) * monomials; intersection computed by the dual: the
    # orthogonal of I_P C under the standard dot product, summed, then dim ∩ = n - dim Σ (I_P C)^⊥.
    perp_rows = []
    for P in matchings(list(range(nv))):
        gens = []
        for (a, b) in P:
            e1 = [0] * nv; e1[a] = 1; e2 = [0] * nv; e2[b] = 1
            gens.append({tuple(e1): 1, tuple(e2): 1})
        rows = list(ideal_rows(gens, nv, r))
        A = np.array(rows, dtype=np.int64) % p
        # null space of A mod p (vectors v with A v = 0) = (I_P C)^⊥
        perp_rows.extend(nullspace_mod_p(A, p))
    s = rank_mod_p(iter(perp_rows), n, p)
    return n - s

def nullspace_mod_p(A, p):
    M = A.copy() % p; rows, cols = M.shape; r = 0; pivcols = []
    for c in range(cols):
        if r == rows: break
        piv = np.nonzero(M[r:, c])[0]
        if len(piv) == 0: continue
        i = r + piv[0]
        if i != r: M[[r, i]] = M[[i, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        for j in np.nonzero(M[:, c])[0]:
            if j != r: M[j] = (M[j] - M[j, c] * M[r]) % p
        pivcols.append(c); r += 1
    free = [c for c in range(cols) if c not in set(pivcols)]
    out = []
    for f in free:
        v = [0] * cols; v[f] = 1
        for i, c in enumerate(pivcols): v[c] = int((-M[i, f]) % p)
        out.append(v)
    return out

P0 = 32003
CTRL = {'Dminus-instead-of-D': 0, 'count-at-r+2': 0, 'T-without-zero': 0}

for (r, k) in [(3, 0), (3, 1), (3, 2), (5, 0), (5, 1), (7, 0), (7, 1), (9, 1), (11, 1), (13, 1)]:
    N = QkEven(k, r + 1)
    check(f'Nr=QkEven r={r} k={k}', Nr(r, 2 * k + 2) == N)
    check(f'Gamma=QkEven r={r} k={k}', Gamma(r, 2 * k + 2) == N)
    gens, nv = DJ_gens(k, r)
    if r ** nv > 2200:
        print(f'r={r} k={k}: N={N} (dimension check skipped, box too large)', flush=True); continue
    for p in (2, 3, 5, 7, P0):
        d = dim_ideal(gens, nv, r, p)
        check(f'dim (D_J) r={r} k={k} p={p}', d == N)
    print(f'r={r} k={k}: dim (D_J) = {N} at p = 2,3,5,7,Q', flush=True)
    # control: D^- (degree r-2) instead of D
    gc, _ = DJ_gens(k, r, deg=r - 2)
    if k >= 1 and dim_ideal(gc, nv, r, P0) != N: CTRL['Dminus-instead-of-D'] += 1
    if N != QkEven(k, r + 3): CTRL['count-at-r+2'] += 1
    # (d) θ step
    dd = poly_D(0, 1, 2, r)
    check(f'theta coeff r={r}', dd.get((r - 1, 0), 0) == 1)
    # (b), (c) in N = 2k+2 variables
    Mg, nN = M_gens(k, r)
    if r ** nN <= 2200:
        dM = dim_ideal(Mg, nN, r, P0)
        check(f'dim M r={r} k={k}', dM == N)
        di = inter_dim(k, r, P0)
        check(f'dim C/∩ >= dim M r={r} k={k}', r ** nN - di >= dM)
        check(f'dim C/∩ = N r={r} k={k}', r ** nN - di == N)
        for p in (2, 3):
            check(f'dim M r={r} k={k} p={p}', dim_ideal(Mg, nN, r, p) == N)
        print(f'   M: dim {dM}, dim C/∩ = {r**nN - di}', flush=True)

# control: a set T with no zero (even box) changes the count
for (r, k) in [(3, 1), (5, 1)]:
    h = (r - 1) // 2
    cnt = 0
    vals = [u for u in range(-h, h + 1) if u != 0] + [h + 1, -(h + 1)]
    vals = vals[:r] if r % 2 == 0 else vals[:r - 1]
    for t in itertools.product(vals, repeat=2 * k + 2):
        if all(t.count(u) == t.count(-u) for u in set(abs(x) for x in vals)): cnt += 1
    if cnt != QkEven(k, r + 1): CTRL['T-without-zero'] += 1

print('controls fired (must be >0 each):', CTRL)
check('controls', all(x > 0 for x in CTRL.values()))
print(f'checks {NCHK} failures {NFAIL}')
print('FIN-OK' if NFAIL == 0 else 'FIN-FAIL')
