# chkE8.py — brute force for Lean piece E8 (q_pfaffian.md): Pfaffians and bordered Pfaffians.
# Grepy Mandalay, 2 Oct 2026. Exact integer arithmetic, no external library.
# Every identity of q_pfaffian.md is tested with the EXPLICIT signs written there, on random integer
# data; controls with a wrong sign must fail.
import itertools, random, sys
random.seed(20261002)
NCHK = 0; NFAIL = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        print('FAIL', name); sys.stdout.flush()

def perm_sign(p):
    p = list(p); s = 1
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]; p[i], p[j] = p[j], p[i]; s = -s
    return s

def matchings(idx):
    if not idx:
        yield []; return
    x = idx[0]
    for t in range(1, len(idx)):
        z = idx[t]; rest = idx[1:t] + idx[t+1:]
        for mm in matchings(rest):
            yield [(x, z)] + mm

def crossings(mm):
    c = 0
    for (a, b) in mm:
        for (c1, d1) in mm:
            if a < c1 < b < d1: c += 1
    return c

def pf_match(A, m):
    # the paper's definition: sum over perfect matchings, sign of the permutation listing the pairs
    if m % 2: return 0
    tot = 0
    for mm in matchings(list(range(m))):
        lst = [v for pr in mm for v in pr]
        sg = perm_sign(lst)
        pr = 1
        for (x, z) in mm: pr *= A[x][z]
        tot += sg * pr
    return tot

def minor(A, m, rem):
    keep = [i for i in range(m) if i not in rem]
    return [[A[i][j] for j in keep] for i in keep], len(keep)

def pf(A, m):
    # the recursive definition of q_pfaffian.md: expansion along the index 0
    if m == 0: return 1
    if m == 1: return 0
    tot = 0
    for j in range(1, m):
        if A[0][j] == 0: continue
        B, mb = minor(A, m, (0, j))
        tot += (-1) ** (j + 1) * A[0][j] * pf(B, mb)
    return tot

def rand_alt(m, lo=-4, hi=4):
    A = [[0] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            v = random.randint(lo, hi); A[i][j] = v; A[j][i] = -v
    return A

def det(M):
    n = len(M)
    if n == 0: return 1
    tot = 0
    for p in itertools.permutations(range(n)):
        pr = perm_sign(p)
        for i in range(n): pr *= M[i][p[i]]
        tot += pr
    return tot

# ---------------- Part A ----------------
# (A0) small values
for _ in range(20):
    A = rand_alt(2); check('A0 m=2', pf(A, 2) == A[0][1])
    A = rand_alt(4); check('A0 m=4', pf(A, 4) == A[0][1]*A[2][3] - A[0][2]*A[1][3] + A[0][3]*A[1][2])
    A = rand_alt(3); check('A0 m=3', pf(A, 3) == 0)
    A = rand_alt(5); check('A0 m=5', pf(A, 5) == 0)
check('A0 m=0', pf([], 0) == 1)
# (A1) the matching formula, and sign = (-1)^crossings
for m in range(0, 9):
    for _ in range(6):
        A = rand_alt(m); check('A1 m=%d' % m, pf(A, m) == pf_match(A, m))
for m in (2, 4, 6, 8):
    for mm in matchings(list(range(m))):
        lst = [v for pr in mm for v in pr]
        check('A1 sign crossings m=%d' % m, perm_sign(lst) == (-1) ** crossings(mm))
# (A2) simultaneous permutation
for m in range(0, 7):
    A = rand_alt(m); base = pf(A, m)
    for s in itertools.permutations(range(m)):
        B = [[A[s[i]][s[j]] for j in range(m)] for i in range(m)]
        check('A2 m=%d' % m, pf(B, m) == perm_sign(s) * base)
for m in (7, 8):
    for _ in range(40):
        A = rand_alt(m); s = list(range(m)); random.shuffle(s)
        B = [[A[s[i]][s[j]] for j in range(m)] for i in range(m)]
        check('A2 m=%d' % m, pf(B, m) == perm_sign(s) * pf(A, m))
# (A3) two equal rows
for m in range(2, 9):
    for i in range(m):
        for j in range(i + 1, m):
            A = rand_alt(m)
            for k in range(m):
                if k not in (i, j):
                    A[j][k] = A[i][k]; A[k][j] = -A[i][k]
            A[i][j] = 0; A[j][i] = 0
            assert all(A[i][k] == A[j][k] for k in range(m))
            check('A3 m=%d' % m, pf(A, m) == 0)
# (A4) expansion along any index x, explicit sign
def eps(x, z):
    return (-1) ** (x + z + 1) if x < z else (-1) ** (x + z)
for m in range(2, 9):
    for _ in range(4):
        A = rand_alt(m); base = pf(A, m)
        for x in range(m):
            tot = 0
            for z in range(m):
                if z == x: continue
                B, mb = minor(A, m, (x, z)); tot += eps(x, z) * A[x][z] * pf(B, mb)
            check('A4 m=%d x=%d' % (m, x), tot == base)
# control: the opposite convention for z < x must fail somewhere
bad = 0
for m in (4, 6):
    A = rand_alt(m); base = pf(A, m)
    for x in range(1, m):
        tot = 0
        for z in range(m):
            if z == x: continue
            B, mb = minor(A, m, (x, z)); tot += (-1) ** (x + z + 1) * A[x][z] * pf(B, mb)
        if tot != base: bad += 1
print('control A4 (same sign on both sides of x): fails in', bad, 'of 8'); check('control A4 fires', bad >= 1)
# (A5) additive and homogeneous in the row-and-column of x
for m in range(2, 8):
    for x in range(m):
        A = rand_alt(m); A1 = [row[:] for row in A]; A2 = [row[:] for row in A]; lam = random.randint(-3, 3)
        for k in range(m):
            if k == x: continue
            u, v = random.randint(-4, 4), random.randint(-4, 4)
            A1[x][k] = u; A1[k][x] = -u; A2[x][k] = v; A2[k][x] = -v
            A[x][k] = u + lam * v; A[k][x] = -(u + lam * v)
        check('A5 m=%d' % m, pf(A, m) == pf(A1, m) + lam * pf(A2, m))

# ---------------- Part B ----------------
def bmat(a, n, c):
    s = len(c); M = [[0] * (n + s) for _ in range(n + s)]
    for i in range(n):
        for j in range(n): M[i][j] = a[i][j]
        for k in range(s):
            M[i][n + k] = c[k][i]; M[n + k][i] = -c[k][i]
    return M, n + s
def bpf(a, n, c):
    M, mm = bmat(a, n, c); return pf(M, mm)
def rand_cols(n, s): return [[random.randint(-4, 4) for _ in range(n)] for _ in range(s)]
def del_var(a, n, c, b):
    keep = [i for i in range(n) if i != b]
    return [[a[i][j] for j in keep] for i in keep], n - 1, [[col[i] for i in keep] for col in c]

cells = [(n, s) for n in range(0, 7) for s in range(0, 5) if n + s <= 8]
for (n, s) in cells:
    a = rand_alt(n); c = rand_cols(n, s); base = bpf(a, n, c)
    # (B0) parity
    if (n + s) % 2: check('B0 parity', base == 0)
    if s > n: check('B0 more borders than variables', base == 0)
    # (B1) permutations of the variables and of the borders
    perms = list(itertools.permutations(range(n))) if n <= 5 else [random.sample(range(n), n) for _ in range(30)]
    for sg in perms:
        a2 = [[a[sg[i]][sg[j]] for j in range(n)] for i in range(n)]; c2 = [[col[sg[i]] for i in range(n)] for col in c]
        check('B1 var n=%d s=%d' % (n, s), bpf(a2, n, c2) == perm_sign(sg) * base)
    for tau in itertools.permutations(range(s)):
        c2 = [c[tau[k]] for k in range(s)]
        check('B1 border n=%d s=%d' % (n, s), bpf(a, n, c2) == perm_sign(tau) * base)
    # (B2) linear in each border; equal borders; expansion along the last border
    for k in range(s):
        u = [random.randint(-4, 4) for _ in range(n)]; v = [random.randint(-4, 4) for _ in range(n)]; lam = random.randint(-3, 3)
        cu = c[:k] + [u] + c[k+1:]; cv = c[:k] + [v] + c[k+1:]; cw = c[:k] + [[u[i] + lam * v[i] for i in range(n)]] + c[k+1:]
        check('B2 linear', bpf(a, n, cw) == bpf(a, n, cu) + lam * bpf(a, n, cv))
    for k in range(s):
        for k2 in range(k + 1, s):
            ce = c[:]; ce[k2] = c[k]; check('B2 equal borders', bpf(a, n, ce) == 0)
    if s >= 1:
        tot = 0
        for b in range(n):
            a2, n2, c2 = del_var(a, n, c[:-1], b)
            tot += (-1) ** (n + s + b) * c[-1][b] * bpf(a2, n2, c2)
        check('B2 expansion last border n=%d s=%d' % (n, s), tot == base)
    # (B4) expansion along a variable x
    for x in range(n):
        a2, n2, c2 = del_var(a, n, c, x)
        newcol = [a[x][b] for b in range(n) if b != x]
        tot = (-1) ** (x + n + s) * bpf(a2, n2, c2 + [newcol])
        for k in range(s):
            tot += (-1) ** (x + n + k + 1) * c[k][x] * bpf(a2, n2, c2[:k] + c2[k+1:])
        check('B4 n=%d s=%d x=%d' % (n, s, x), tot == base)
# (B3) n = s: +-det, sign (-1)^(s(s-1)/2), independent of a
for s in range(0, 5):
    for _ in range(6):
        a = rand_alt(s); c = rand_cols(s, s)
        Mx = [[c[k][i] for k in range(s)] for i in range(s)]
        check('B3 s=%d' % s, bpf(a, s, c) == (-1) ** (s * (s - 1) // 2) * det(Mx))
bad = 0
for _ in range(6):
    a = rand_alt(2); c = rand_cols(2, 2); Mx = [[c[k][i] for k in range(2)] for i in range(2)]
    if bpf(a, 2, c) != det(Mx): bad += 1
print('control B3 (sign +1 at s = 2): fails in', bad, 'of 6'); check('control B3 fires', bad >= 1)
# (B5) Laplace: n = s + 2*kappa
def lap(a, n, c):
    s = len(c); tot = 0
    for S in itertools.combinations(range(n), s):
        comp = [i for i in range(n) if i not in S]
        sgS = (-1) ** (sum(S) - s * (s - 1) // 2)
        Mx = [[c[k][i] for k in range(s)] for i in S]
        ac = [[a[i][j] for j in comp] for i in comp]
        tot += sgS * det(Mx) * pf(ac, len(comp))
    return tot
signs = {}
for (n, s) in cells:
    if (n - s) % 2 or n < s: continue
    for _ in range(4):
        a = rand_alt(n); c = rand_cols(n, s); L = lap(a, n, c); base = bpf(a, n, c)
        want = (-1) ** (s * (s - 1) // 2)
        check('B5 n=%d s=%d' % (n, s), base == want * L)
        if L != 0: signs[(n, s)] = base // L
print('B5 measured signs (n, s) -> sign:', sorted(signs.items()))
# control for (B4): theta with the opposite sign
bad = 0; tot_c = 0
for (n, s) in [(3, 1), (4, 2), (5, 1), (4, 0)]:
    a = rand_alt(n); c = rand_cols(n, s); base = bpf(a, n, c)
    for x in range(n):
        a2, n2, c2 = del_var(a, n, c, x); newcol = [a[x][b] for b in range(n) if b != x]
        tot = -(-1) ** (x + n + s) * bpf(a2, n2, c2 + [newcol])
        for k in range(s): tot += (-1) ** (x + n + k + 1) * c[k][x] * bpf(a2, n2, c2[:k] + c2[k+1:])
        tot_c += 1
        if tot != base: bad += 1
print('control B4 (theta reversed): fails in', bad, 'of', tot_c); check('control B4 fires', bad >= 1)
# control for (B2): eta with the parity shifted
bad = 0; tot_c = 0
for (n, s) in [(3, 1), (4, 2), (2, 2), (5, 3)]:
    a = rand_alt(n); c = rand_cols(n, s); base = bpf(a, n, c); tot = 0
    for b in range(n):
        a2, n2, c2 = del_var(a, n, c[:-1], b); tot += (-1) ** (n + s + b + 1) * c[-1][b] * bpf(a2, n2, c2)
    tot_c += 1
    if tot != base: bad += 1
print('control B2 (eta shifted): fails in', bad, 'of', tot_c); check('control B2 fires', bad >= 1)

# ---------------- Part C ----------------
def Dab(q, a, b): return sum((-1) ** u * a ** u * b ** (q - 2 - u) for u in range(q - 1))
for r in (3, 5, 7):
    Dp = lambda a, b: Dab(r + 1, a, b)      # D
    Dm = lambda a, b: Dab(r, a, b)          # D^-
    for n in range(0, 6):
        for trial in range(3):
            y = [random.randint(-3, 3) for _ in range(n)]
            a = [[Dm(y[i], y[j]) for j in range(n)] for i in range(n)]
            check('C0 alternating r=%d' % r, all(a[i][i] == 0 for i in range(n)) and all(a[i][j] == -a[j][i] for i in range(n) for j in range(n)))
            for s in range(0, 4):
                if n + s + 1 > 8: continue
                E = sorted(random.sample(range(r), s)) if s <= r else None
                if E is None: continue
                cE = [[y[i] ** e for i in range(n)] for e in E]
                x = random.randint(-3, 3)
                colDm = [Dm(x, y[b]) for b in range(n)]; colD = [Dp(x, y[b]) for b in range(n)]
                # (C1)
                lhs = bpf(a, n, cE + [colDm])
                rhs = -sum((-1) ** u * x ** (r - 2 - u) * bpf(a, n, cE + [[y[i] ** u for i in range(n)]]) for u in range(r - 1))
                check('C1 r=%d n=%d s=%d' % (r, n, s), lhs == rhs)
                # (C2)
                lhs2 = bpf(a, n, cE + [colD])
                rhs2 = sum((-1) ** u * x ** (r - 1 - u) * bpf(a, n, cE + [[y[i] ** u for i in range(n)]]) for u in range(r))
                check('C2 r=%d n=%d s=%d' % (r, n, s), lhs2 == rhs2)
                # (C3)
                check('C3 r=%d' % r, lhs2 == bpf(a, n, cE + [[y[i] ** (r - 1) for i in range(n)]]) - x * lhs)
                # (C4) a repeated exponent gives 0; a new exponent is sorted in with the sign (-1)^{#{e in E : e > u}}
                for u in range(r):
                    val = bpf(a, n, cE + [[y[i] ** u for i in range(n)]])
                    if u in E: check('C4 repeated', val == 0)
                    else:
                        E2 = sorted(E + [u]); cE2 = [[y[i] ** e for i in range(n)] for e in E2]
                        check('C4 sorted', val == (-1) ** sum(1 for e in E if e > u) * bpf(a, n, cE2))
    # (C5) |N| = s, E = {0..s-1}: +- Vandermonde
    for s in range(0, 5):
        y = random.sample(range(-5, 6), s)
        a = [[Dm(y[i], y[j]) for j in range(s)] for i in range(s)]
        cE = [[y[i] ** e for i in range(s)] for e in range(s)]
        vdm = 1
        for i in range(s):
            for j in range(i + 1, s): vdm *= (y[j] - y[i])
        check('C5 r=%d s=%d' % (r, s), bpf(a, s, cE) == (-1) ** (s * (s - 1) // 2) * vdm)
# the paper's examples of Section 8.4 (r = 3, 5): Pf_{{r-1}}({1,2,3}) and ((1,1),1) on three indices
for r in (3, 5):
    Dm = lambda a, b: Dab(r, a, b)
    for _ in range(10):
        y = [random.randint(-3, 3) for _ in range(3)]
        a = [[Dm(y[i], y[j]) for j in range(3)] for i in range(3)]
        v = bpf(a, 3, [[y[i] ** (r - 1) for i in range(3)]])
        w = y[2] ** (r - 1) * Dm(y[0], y[1]) - y[1] ** (r - 1) * Dm(y[0], y[2]) + y[0] ** (r - 1) * Dm(y[1], y[2])
        check('example (empty,1) on three indices', v == w or v == -w)
        v2 = bpf(a, 3, [[1, 1, 1]])
        w2 = Dm(y[0], y[1]) - Dm(y[0], y[2]) + Dm(y[1], y[2])
        check('example ((1,1),1) on three indices', v2 == w2 or v2 == -w2)

print('TOTAL checks:', NCHK, ' failures:', NFAIL)
print('FIN-OK' if NFAIL == 0 else 'FIN-WITH-FAILURES')
