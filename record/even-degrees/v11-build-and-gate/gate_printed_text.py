# Gate of the printed text of PAPER_OFICIAL_v11, sections 8-10 (Grepy Chats, 2 Oct 2026).
# Everything is recomputed from the statements as printed; no code of the constructor or of the
# cold reader is used.  Exact linear algebra over F_p.
# ESTIMATE (written before the run): largest matrix 15 360 x 1 024 int32 (63 MB) plus one
# temporary of the same size; peak < 400 MB; time < 4 min.
import sys, itertools
import numpy as np
from math import comb, factorial
from fractions import Fraction

FAIL = []
def check(name, cond, info=''):
    print(('  ok   ' if cond else '  FAIL ') + name + (' : ' + str(info) if info != '' else ''))
    if not cond: FAIL.append(name)
    sys.stdout.flush()

# ---------- linear algebra mod p ----------
def rref(M, p):
    M = np.array(M, dtype=np.int32) % p
    if M.size == 0: return M.reshape(0, M.shape[1] if M.ndim == 2 else 0), []
    M = M[np.any(M != 0, axis=1)]
    rows, cols = M.shape
    r = 0; piv = []
    for c in range(cols):
        if r >= rows: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        if i != r: M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), -1, p)
        if inv != 1: M[r] = (M[r] * inv) % p
        col = M[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr): M[nzr] = (M[nzr] - np.outer(col[nzr], M[r])) % p
        r += 1; piv.append(c)
    return M[:r].copy(), piv

def rank(M, p): return len(rref(M, p)[1])

def nullspace(M, p, cols):
    R, piv = rref(M, p)
    free = [c for c in range(cols) if c not in set(piv)]
    out = np.zeros((len(free), cols), dtype=np.int32)
    for i, f in enumerate(free):
        out[i, f] = 1
        for j, c in enumerate(piv):
            out[i, c] = (-int(R[j, f])) % p
    return out

def same_span(A, B, p):
    RA, pa = rref(A, p); RB, pb = rref(B, p)
    return pa == pb and RA.shape == RB.shape and bool(np.all(RA == RB))

# ---------- polynomials in a box ring F_p[x_1..x_n]/(x_i^r) as dense arrays ----------
def mono(n, r, exps):            # exps: dict index -> exponent
    a = np.zeros((r,) * n, dtype=np.int64)
    idx = [0] * n
    for i, e in exps.items():
        if e >= r: return a
        idx[i] = e
    a[tuple(idx)] = 1
    return a

def shift(g, e, r):              # multiply dense g by the monomial x^e in the box
    n = g.ndim
    res = np.zeros_like(g)
    src = tuple(slice(0, r - e[i]) for i in range(n))
    dst = tuple(slice(e[i], r) for i in range(n))
    res[dst] = g[src]
    return res

def mul(f, g, r, p):             # product in the box
    res = np.zeros_like(f)
    for e in zip(*np.nonzero(f)):
        res = (res + int(f[e]) * shift(g, e, r)) % p
    return res

def ideal_rows(gens, r):
    n = gens[0].ndim
    rows = []
    for g in gens:
        for e in itertools.product(range(r), repeat=n):
            s = shift(g, e, r)
            if s.any(): rows.append(s.reshape(-1))
    return np.array(rows, dtype=np.int32) if rows else np.zeros((0, r ** n), dtype=np.int32)

def D(n, r, a, b, p, signed=True):   # D_r(x_a, x_b) = sum (-1)^u x_a^u x_b^(r-1-u)
    res = np.zeros((r,) * n, dtype=np.int64)
    for u in range(r):
        res = (res + ((-1) ** u if signed else 1) * mono(n, r, {a: u, b: r - 1 - u})) % p
    return res

def var(n, r, i): return mono(n, r, {i: 1})

def matchings(S):
    S = list(S)
    if not S: yield []; return
    a = S[0]
    for i in range(1, len(S)):
        b = S[i]
        for rest in matchings(S[1:i] + S[i + 1:]):
            yield [(a, b)] + rest

def N_count(r, n):               # n! [x^n] e^x I_0(2x)^h,  r = 2h+1
    h = (r - 1) // 2
    I0 = [Fraction(1, factorial(b) ** 2) if True else 0 for b in range(n // 2 + 1)]
    ser = [Fraction(0)] * (n + 1); ser[0] = Fraction(1)
    for _ in range(h):
        new = [Fraction(0)] * (n + 1)
        for i, c in enumerate(ser):
            if c:
                for b, d in enumerate(I0):
                    if i + 2 * b <= n: new[i + 2 * b] += c * d
        ser = new
    tot = sum(ser[i] * Fraction(1, factorial(n - i)) for i in range(n + 1))
    return int(tot * factorial(n))

def elem_sym(n, r, j, p):
    res = np.zeros((r,) * n, dtype=np.int64)
    for S in itertools.combinations(range(n), j):
        res = (res + mono(n, r, {i: 1 for i in S})) % p
    return res

# =====================================================================
print('T1  section 8.9: r = 3, k = 1, slices of (D(y2,y3), D(y1,y3), D(y1,y2))')
for p in (2, 3, 5):
    n, r = 3, 3
    gens = [D(n, r, 1, 2, p), D(n, r, 0, 2, p), D(n, r, 0, 1, p)]
    M = ideal_rows(gens, r)
    # order the columns by the degree in y_1 (index 0), highest first
    exps = list(itertools.product(range(r), repeat=n))
    order = sorted(range(len(exps)), key=lambda i: -exps[i][0])
    R, piv = rref(M[:, order], p)
    sl = [0, 0, 0]
    for c in piv: sl[exps[order[c]][0]] += 1
    check('p=%d dim = 19 and slices (W_0,W_1,W_2) = (3,7,9)' % p, len(piv) == 19 and sl == [3, 7, 9], (len(piv), sl))

# =====================================================================
print('T2  Lemma 8.12 and Corollary 8.13: the two forms, the map theta')
for (k, r) in ((1, 3), (2, 3), (1, 5)):
    for p in (2, 3, 5):
        N = 2 * k + 2
        target = N_count(r, N)
        # M in N variables x_0 (index 0), y_1..y_{2k+1}
        gensM = []
        for P in matchings(range(N)):
            g = mono(N, r, {})
            for (a, b) in P: g = mul(g, D(N, r, a, b, p), r, p)
            gensM.append(g)
        RM, pivM = rref(ideal_rows(gensM, r), p)
        # the ideal (D_J) in 2k+1 variables: matchings of {0..2k+1}, pairs avoiding 0
        n1 = N - 1
        gensJ = []
        for P in matchings(range(N)):
            g = mono(n1, r, {})
            for (a, b) in P:
                if a != 0: g = mul(g, D(n1, r, a - 1, b - 1, p), r, p)
            gensJ.append(g)
        RJ, pivJ = rref(ideal_rows(gensJ, r), p)
        # theta: coefficient of x_0^(r-1)
        th = RM.reshape((len(pivM),) + (r,) * N)[:, r - 1].reshape(len(pivM), -1)
        inj = rank(th, p) == len(pivM)
        onto = same_span(th, RJ, p)
        check('(k,r,p)=(%d,%d,%d): dim M = dim (D_J) = N_r(N) = %d, theta injective, image = (D_J)' % (k, r, p, target),
              len(pivM) == target and len(pivJ) == target and inj and onto, (len(pivM), len(pivJ), inj, onto))

# =====================================================================
print('T3  Corollary 10.8: sum of the D_J C  =  ann(e_odd);  intersection of the I_J C  =  (e_odd) C')
for (r, N) in ((3, 4), (3, 6), (5, 4)):
    for p in (3, 5, 7, 2):
        target = N_count(r, N)
        dimC = r ** N
        Ms = list(matchings(range(N)))
        gens = []
        for P in Ms:
            g = mono(N, r, {})
            for (a, b) in P: g = mul(g, D(N, r, a, b, p), r, p)
            gens.append(g)
        A = ideal_rows(gens, r)
        RA, pivA = rref(A, p)
        eodd = [elem_sym(N, r, j, p) for j in range(1, N + 1, 2)]
        Y = ideal_rows(eodd, r)                                  # (e_odd) C
        RY, pivY = rref(Y, p)
        # ann(e_odd): v with e_j * v = 0; the matrix of multiplication by e_j
        blocks = []
        exps = list(itertools.product(range(r), repeat=N))
        for e in eodd:
            cols = np.zeros((dimC, dimC), dtype=np.int32)
            for i, ex in enumerate(exps):
                cols[:, i] = shift(e, ex, r).reshape(-1) % p     # image of the monomial x^ex
            blocks.append(cols)
        Bann = nullspace(np.vstack(blocks), p, dimC)
        # intersection of the I_J C through orthogonal complements
        perps = []
        for P in Ms:
            V = ideal_rows([(var(N, r, a) + var(N, r, b)) % p for (a, b) in P], r)
            perps.append(nullspace(V, p, dimC))
        X = nullspace(np.vstack(perps), p, dimC)
        RX, pivX = rref(X, p)
        if p != 2:
            ok = (len(pivA) == target and same_span(RA, Bann, p)
                  and dimC - len(pivX) == target and dimC - len(pivY) == target and same_span(RX, RY, p))
            check('(r,N,p)=(%d,%d,%d): both equalities, colength %d' % (r, N, p, target), ok,
                  (len(pivA), Bann.shape[0], dimC - len(pivX), dimC - len(pivY)))
        else:
            info = (len(pivA), dimC - len(pivX), dimC - len(pivY))
            if (r, N) == (3, 4):
                check('(r,N,p)=(3,4,2): colengths 19 (intersection) and 21 (e_odd)', info == (19, 19, 21), info)
            else:
                check('(r,N,p)=(%d,%d,2): sum = colength of the intersection = N_r(N) (Theorem O in char 2)' % (r, N),
                      info[0] == target and info[1] == target, info)

# =====================================================================
print('T4  one matching removed, r = 3, k = 2 (five variables): dimension 140 for each of the 15')
for p in (2, 3):
    n1, r = 5, 3
    Ms = list(matchings(range(6)))
    gensJ = []
    for P in Ms:
        g = mono(n1, r, {})
        for (a, b) in P:
            if a != 0: g = mul(g, D(n1, r, a - 1, b - 1, p), r, p)
        gensJ.append(g)
    rowsJ = [ideal_rows([g], r) for g in gensJ]
    full = rank(np.vstack(rowsJ), p)
    dims = [rank(np.vstack(rowsJ[:i] + rowsJ[i + 1:]), p) for i in range(15)]
    check('p=%d: full 141, each of the 15 removals 140' % p, full == 141 and dims == [140] * 15, (full, sorted(set(dims))))

# =====================================================================
print('T5  Proposition 9.2: m = q = 2^v over F_2')
p = 2
for (k, q) in ((1, 4), (2, 4), (1, 8)):
    n = 2 * k + 1
    one = mono(n, q, {})
    s = [var(n, q, i) for i in range(n)]
    target = N_count(q - 1, 2 * k + 2)
    psi, psi2, Lq, YD = [], [], [], []
    Y = mono(n, q, {i: 1 for i in range(n)})
    step1 = True; step3 = True; lead = True
    for P in matchings(range(2 * k + 2)):
        # literal generator: tau_J * prod phi(t_j t_l), t = 1 + s
        g = one.copy(); g2 = one.copy(); L = one.copy(); DJ = one.copy()
        for (a, b) in P:
            if a == 0:
                g = mul(g, s[b - 1], q, p); g2 = mul(g2, s[b - 1], q, p); L = mul(L, s[b - 1], q, p)
            else:
                sj, sl = s[a - 1], s[b - 1]
                u = mul((one + sj) % p, (one + sl) % p, q, p)
                phi = one.copy(); pw = one.copy()
                for i in range(1, q):
                    pw = mul(pw, u, q, p); phi = (phi + pw) % p
                g = mul(mul(g, sl, q, p), phi, q, p)
                w = (sj + sl + mul(sj, sl, q, p)) % p
                wq = one.copy()
                for i in range(q - 1): wq = mul(wq, w, q, p)
                g2 = mul(mul(g2, sl, q, p), wq, q, p)
                # (s_j + s_l)^(q-1) is homogeneous: the box truncation and the lowest component commute
                lin = (sj + sl) % p; lq = one.copy()
                for i in range(q - 1): lq = mul(lq, lin, q, p)
                L = mul(mul(L, sl, q, p), lq, q, p)
                # D_{q-1}(s_j, s_l) over F_2, as an element of the box q (exponents <= q-2)
                d = np.zeros_like(one)
                for wv in range(q - 1): d = (d + mono(n, q, {a - 1: wv, b - 1: q - 2 - wv})) % p
                DJ = mul(DJ, d, q, p)
        psi.append(g); psi2.append(g2); Lq.append(L); YD.append(mul(Y, DJ, q, p))
        step1 = step1 and bool(np.all(g == g2))
        step3 = step3 and bool(np.all(L == YD[-1]))
        # lowest homogeneous component of psi_J in B
        deg = np.add.outer.reduce([np.arange(q)] * n) if False else sum(np.meshgrid(*[np.arange(q)] * n, indexing='ij'))
        if g.any():
            dmin = int(deg[g != 0].min())
            low = np.where(deg == dmin, g, 0)
            lead = lead and (not L.any() or bool(np.all(low == L)))
    exps = list(itertools.product(range(q), repeat=n))
    degs = [sum(e) for e in exps]
    order = sorted(range(len(exps)), key=lambda i: degs[i])
    RI, pivI = rref(ideal_rows(psi, q)[:, order], p)
    hf_in = {}
    for c in pivI: hf_in[degs[order[c]]] = hf_in.get(degs[order[c]], 0) + 1
    RL, pivL = rref(ideal_rows(Lq, q)[:, order], p)
    hf_L = {}
    for c in pivL: hf_L[degs[order[c]]] = hf_L.get(degs[order[c]], 0) + 1
    # Theorem O ideal at the box r = q - 1
    r = q - 1
    gensJ = []
    for P in matchings(range(2 * k + 2)):
        g = mono(n, r, {})
        for (a, b) in P:
            if a != 0: g = mul(g, D(n, r, a - 1, b - 1, p, signed=False), r, p)
        gensJ.append(g)
    dO = rank(ideal_rows(gensJ, r), p)
    ok = step1 and step3 and lead and len(pivI) == target and len(pivL) == target and hf_in == hf_L and dO == target
    check('(k,q)=(%d,%d): Step 1, in(psi_J) = L_J = Y*D_J, dim I = dim (L_J)B = dim Theorem-O ideal = %d, HF(in I) = HF((L_J)B)' % (k, q, target),
          ok, (step1, step3, lead, len(pivI), len(pivL), dO, [hf_in[d] for d in sorted(hf_in)]))

# =====================================================================
print('T6  the table of section 9.1 and Example 9.14')
def Q_even(k, m): return N_count(m - 1, 2 * k + 2)
table = {4: [19, 141, 1107, 8953, 73789], 6: [61, 1001, 18733, 375745, 7858225],
         8: [127, 3301, 103279, 3595177, 133789789], 10: [217, 7761, 345465, 17605249, 980612161],
         12: [331, 15101, 876331, 59415961, 4481629021], 16: [631, 41301, 3529863, 361612105, 42214788925]}
check('table of Q_k(m), m = 4..16 even, k = 1..5', all([Q_even(k, m) for k in range(1, 6)] == v for m, v in table.items()))
check('Q_1(m) = 3m^2 - 9m + 7 for even m <= 40', all(Q_even(1, m) == 3 * m * m - 9 * m + 7 for m in range(4, 41, 2)))
def trinomial(n):
    c = [1]
    for _ in range(n): c = [sum(c[j - i] for i in range(3) if 0 <= j - i < len(c)) for j in range(len(c) + 2)]
    return c[n]
check('m = 4: central trinomial coefficients of 2k+2', all(Q_even(k, 4) == trinomial(2 * k + 2) for k in range(1, 8)))
# brute force count for (k, m) = (1, 6): 4-tuples in Z/6 minus 0 that split into pairs a, -a
def splits(t, m):
    t = list(t)
    if not t: return True
    a = t[0]
    for i in range(1, len(t)):
        if (a + t[i]) % m == 0 and splits(t[1:i] + t[i + 1:], m): return True
    return False
tuples = [t for t in itertools.product(range(1, 6), repeat=4) if splits(t, 6)]
check('direct count at (k,m) = (1,6) is 61', len(tuples) == 61, len(tuples))
by3 = {}; by2 = {}
for t in tuples:
    c = tuple(x % 2 for x in t)          # colour at p = 3: the component in mu_2 (0 = colour 1, 1 = colour -1)
    by3.setdefault(c, 0); by3[c] += 1
    c = tuple(x % 3 for x in t)          # colour at p = 2: the component in mu_3
    by2.setdefault(c, 0); by2[c] += 1
agg3 = {}
for c, v in by3.items():
    key = (c.count(0), c.count(1)); agg3.setdefault(key, []).append(v)
agg2 = {}
for c, v in by2.items():
    key = (c.count(0), c.count(1), c.count(2)); agg2.setdefault(key, []).append(v)
check('p = 3: (4,0): 1 x 6, (2,2): 6 x 6, (0,4): 1 x 19',
      {k: (len(v), set(v)) for k, v in agg3.items()} == {(4, 0): (1, {6}), (2, 2): (6, {6}), (0, 4): (1, {19})},
      {k: (len(v), sorted(set(v))) for k, v in agg3.items()})
check('p = 2: (4,0,0): 1 x 1, (2,1,1): 12 x 2, (0,2,2): 6 x 6; 19 compatible colourings',
      {k: (len(v), set(v)) for k, v in agg2.items()} == {(4, 0, 0): (1, {1}), (2, 1, 1): (12, {2}), (0, 2, 2): (6, {6})}
      and len(by2) == 19, {k: (len(v), sorted(set(v))) for k, v in agg2.items()})

print()
print('FAILURES: %d %s' % (len(FAIL), FAIL))
print('FIN-OK')
