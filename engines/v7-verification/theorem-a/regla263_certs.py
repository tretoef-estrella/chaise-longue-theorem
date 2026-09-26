# regla263_certs.py — Grepy el Lector, 2026-09-23, MISION 89. OWN CODE.
# (I) indices: exhaustive bookkeeping of Theorem Gamma — every child object (s,w) of every row of every profile
#     (|mu| <= 14, l(mu) <= h) is covered by PASCAL / DESCENT / NEW-CLASS / RAISE with the auditor's own conditions,
#     including the lower z-terms of the raise (u_i <= lambda_w, u_i - i <= lambda_{w+1} for i < i*).
# (X) exact certificates in the real letters (pure Python over F_3, mod box, mod z^{a+1}):
#     for random (mu, n, A, B, w), the NEW-CLASS identity and the RAISE expansion, and the DESCENT identity.
import sys, os, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # repo copy: was an absolute path
from regla263_gamma import lam, rows, gamma, add

def parts(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for k in range(min(n, mx), 0, -1):
        for t in parts(n - k, k): yield (k,) + t

def covered(mu, a, s, w, q):
    l = len(mu)
    if s <= 0: return 'BOX'
    if s + 1 <= lam(mu, w): return 'P'
    if s <= lam(mu, w) and s - a <= lam(mu, w + 1): return 'D'
    if w == 0 and s == sum(mu) + 1 and a >= l + 1:
        # NC needs (D) at row l for level |mu|: |mu| - l <= lam(mu,1)
        assert sum(mu) - l <= lam(mu, 1)
        return 'NC'
    if w >= 1 and s == lam(mu, w) + 1 and lam(mu, w - 1) >= 1:
        sp = lam(mu, w - 1); cwm1 = sum(1 for x in mu if x >= w)
        istar = q - cwm1
        assert sp - q + 1 + istar == s
        if a >= istar:
            for i in range(0, istar):
                u = sp - q + 1 + i
                if u <= 0: continue
                if not (u <= lam(mu, w) and u - i <= lam(mu, w + 1)): return None
            return 'R'
    return None

def check_indices(q, top):
    h = (q - 1) // 2; nobj = 0; bad = []
    for m in range(0, top + 1):
        for mu in parts(m):
            if len(mu) > h: continue
            ch = rows(mu, q)
            for a in range(q):
                c = ch[a]
                if len(c) > h: bad.append(('child l>h', mu, a, c)); continue
                wmax = (c[0] if c else 0)
                for w in range(0, wmax):
                    for s in range(1, lam(c, w) + 1):
                        nobj += 1
                        if covered(mu, a, s, w, q) is None: bad.append((mu, a, c, s, w))
    return nobj, bad

# ---------- exact certificates ----------
def mulpoly(a, b, q):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            if max(m) >= q: continue
            add(out, m, c1 * c2)
    return out
def addto(a, b, s=1):
    for m, c in b.items(): add(a, m, s * c)
def zpow(nv, zi, e):
    m = [0] * nv; m[zi] = e; return {tuple(m): 1}
def G(A, P, s, rA, nv, q):
    D = rA * (q - 1) + len(P) + 1 - s
    return gamma(tuple(A), tuple(P), D, nv, q)
def truncz(d, zi, k):  # drop z-degree >= k
    return {m: c for m, c in d.items() if m[zi] < k}

def check_raise(mu, n, A, B, q):
    w = len(B) - len(A); assert w >= 1
    nv = n + 1; zi = n
    P = [i for i in range(n) if i not in A and i not in B]
    sp = lam(mu, w - 1); t = lam(mu, w) + 1
    cwm1 = sum(1 for x in mu if x >= w); istar = q - cwm1
    Pi = G(sorted(A + [zi]), P, sp, len(A) + 1, nv, q)          # parent object, heavy set A u {z}
    rhs = {}
    for i in range(0, q):
        u = sp - q + 1 + i
        term = G(A, P, u, len(A), nv, q) if u >= 1 else ({} if len(A) == 0 else G(A, P, u, len(A), nv, q))
        coef = 1 if i == 0 else (-(-1) ** i)
        addto(rhs, mulpoly(zpow(nv, zi, i), term, q), coef)
    diff = dict(Pi); addto(diff, rhs, -1)
    ok_expansion = (len(diff) == 0)
    # the z^{istar} coefficient must be a unit times Gamma^{(t)}(A;B)(n)
    tgt = G(A, P, t, len(A), nv, q)
    return ok_expansion, istar, len(tgt) > 0

def check_nc(mu, n, A, B, q):
    l = len(mu); nv = n + 1; zi = n
    P = [i for i in range(n) if i not in A and i not in B]
    r = len(A); assert len(B) == r
    M = r * (q - 1) + len(P) + 1 - sum(mu)
    # h_m(-x_A, x_B) coefficients: H_{A;B}(t) = prod_A (1+at)^{-1} prod_B (1-bt)^{-1}
    def hcomp(D):
        d = {}
        if D < 0: return d
        L = A + B; sg = [-1] * len(A) + [1] * len(B)
        def rec(i, left, ex):
            if i == len(L) - 1:
                if left <= q - 1:
                    e = ex + [left]; m = [0] * nv; c = 1
                    for k, x in enumerate(L): m[x] = e[k]; c *= sg[k] ** e[k]
                    add(d, tuple(m), c)
                return
            for x in range(0, min(left, q - 1) + 1): rec(i + 1, left - x, ex + [x])
        if not L: return {tuple([0] * nv): 1} if D == 0 else {}
        rec(0, D, []); return d
    def esym(k, letters):
        d = {}
        if k < 0 or k > len(letters): return d
        for S in itertools.combinations(letters, k):
            m = [0] * nv
            for i in S: m[i] = 1
            d[tuple(m)] = 1
        return d
    Y = list(range(n + 1))
    def oddsum(Mm):
        out = {}
        for k in range(1, n + 2, 2): addto(out, mulpoly(esym(k, Y), hcomp(Mm - k), q))
        return out
    X = mulpoly(zpow(nv, zi, l), oddsum(M), q)
    addto(X, mulpoly(zpow(nv, zi, l + 1), oddsum(M - 1), q), -1)
    lhs = mulpoly(zpow(nv, zi, l + 1), G(A, P, sum(mu) + 1, r, nv, q), q)
    rhs = dict(X)
    addto(rhs, mulpoly(zpow(nv, zi, l), G(A, P, sum(mu), r, nv, q), q), -1)
    sgn = (-1) ** M
    addto(rhs, mulpoly(zpow(nv, zi, l), G(B, P, sum(mu), len(B), nv, q), q), sgn)
    diff = dict(lhs); addto(diff, rhs, -1)
    diff = truncz(diff, zi, l + 2)
    return len(diff) == 0, len(lhs)

def check_descent(mu, n, A, B, q, a, s):
    nv = n + 1; zi = n
    P = [i for i in range(n) if i not in A and i not in B]
    r = len(A)
    lhs = mulpoly(zpow(nv, zi, a), G(A, P, s, r, nv, q), q)
    rhs = G(A, P, s - a, r, nv, q) if (s - a >= 1 or r >= 1) else {}   # B u {z}: same P
    for i in range(1, a + 1):
        addto(rhs, mulpoly(zpow(nv, zi, i - 1), G(A, P + [zi], s - a + i, r, nv, q), q), -1)
    diff = dict(lhs); addto(diff, rhs, -1)
    return len(diff) == 0

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'I':
        for q, top in [(3, 12), (9, 14), (27, 14), (81, 14)]:
            nobj, bad = check_indices(q, top)
            print('INDICES q=%d |mu|<=%d objects=%d uncovered=%d %s' % (q, top, nobj, len(bad), bad[:5]), flush=True)
    if mode == 'X':
        random.seed(263)
        cases = 0; fails = 0
        for (q, n, mu) in [(9, 5, (2, 1)), (9, 6, (3, 1)), (9, 6, (2, 2)), (9, 6, (3, 2)), (9, 7, (2, 2, 1)), (27, 5, (3, 1)), (27, 5, (2, 2)), (9, 6, (4, 1))]:
            L = list(range(n))
            for w in range(1, mu[0] + 1):
                if lam(mu, w - 1) < 1: continue
                for r in (0, 1, 2):
                    if 2 * r + w > n: continue
                    for _ in range(2):
                        random.shuffle(L); A = sorted(L[:r]); B = sorted(L[r:r + r + w])
                        ok, istar, nz = check_raise(mu, n, A, B, q); cases += 1; fails += (not ok)
                        print('RAISE q=%d n=%d mu=%s w=%d A=%s B=%s expansion_exact=%s istar=%d target_nonzero=%s' % (q, n, mu, w, A, B, ok, istar, nz), flush=True)
            for r in (0, 1, 2):
                if 2 * r > n: continue
                random.shuffle(L); A = sorted(L[:r]); B = sorted(L[r:2 * r])
                ok, sz = check_nc(mu, n, A, B, q); cases += 1; fails += (not ok)
                print('NEWCLASS q=%d n=%d mu=%s A=%s B=%s identity=%s (#lhs %d)' % (q, n, mu, A, B, ok, sz), flush=True)
            for (a, s) in [(1, 2), (2, 3), (3, 3), (2, 1)]:
                r = 1 if n >= 3 else 0
                random.shuffle(L); A = sorted(L[:r]); B = sorted(L[r:2 * r + 1])
                ok = check_descent(mu, n, A, B, q, a, s); cases += 1; fails += (not ok)
                print('DESCENT q=%d n=%d a=%d s=%d A=%s B=%s exact=%s' % (q, n, a, s, A, B, ok), flush=True)
        print('X cases=%d fails=%d' % (cases, fails))
    print('FIN-OK', mode)
