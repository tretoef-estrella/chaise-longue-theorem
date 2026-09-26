# regla262_verif.py — Grepy el Lector, 2026-09-23, MISION 88 (audit of INFORME_13).
# Independent re-checks, own code (not the Fable's scripts), exact over F_3 mod box, pure Python dicts:
#  (T) Theorem T in the REAL n letters: T1 := sum_{k odd} h_{N+1-k} e_k(y) and
#      T2 := sum_{k odd} (h_{N+1-k} e_{k-1}(y) - h_{N-k} e_k(y)), h = h(-x_A, x_B);
#      check z*T1 in N_0(n+1) monomial by monomial and T2 == 2^{r+1}(-1)^n G_r(A;B) exactly.
#  (R) Theorem R: Psi := (-1)^n Omega - z^{q-4} psi_jl - y_j^{q-4} psi_zl, mod box + (z^{q-1});
#      check Psi - z^{q-2} phi_jl has only monomials in Mon (#zeros <= #(q-1)-exponents + 1).
#  (Z) Lemma Z: sum_{k odd} e_k(y) h_{M-k}(-x_A, x_E) == (-1)^{|P|-1} 2^r x_A^{q-1} e_{|P|-1}(P) mod box + L_{r-1}.
#  (C) Dictionary counts: |W_mu(n)| by EGF (exact fractions), recursion over the row dictionary, all 71 cells of row k=4.
import sys, itertools
from fractions import Fraction
from math import factorial
P3 = 3
def add(d, m, c):
    c %= P3
    if c == 0: return
    v = (d.get(m, 0) + c) % P3
    if v: d[m] = v
    else: d.pop(m, None)
def mul(a, b, q):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            if max(m) >= q: continue
            add(out, m, c1 * c2)
    return out
def addto(a, b, s=1):
    for m, c in b.items(): add(a, m, s * c)
def elem(k, vars_, nv):
    d = {}
    if k < 0 or k > len(vars_): return d
    for S in itertools.combinations(vars_, k):
        m = [0] * nv
        for i in S: m[i] = 1
        d[tuple(m)] = 1
    return d
def hcomp(D, letters, signs, nv, q):
    # complete homogeneous h_D in the given letters with letter i replaced by signs[i]*x_i; exponents <= q-1 only
    d = {}
    if D < 0: return d
    L = len(letters)
    def rec(i, left, exps):
        if i == L - 1:
            if left <= q - 1:
                e = exps + [left]; m = [0] * nv; c = 1
                for t, x in enumerate(letters):
                    m[x] = e[t]; c *= signs[t] ** e[t]
                add(d, tuple(m), c)
            return
        for a in range(0, min(left, q - 1) + 1):
            rec(i + 1, left - a, exps + [a])
    rec(0, D, [])
    return d
def mono(nv, ex):
    m = [0] * nv
    for i, e in ex.items(): m[i] = e
    return tuple(m)

def checkT(r, n, q):
    nv = n; A = list(range(r)); B = list(range(r, 2 * r)); P = list(range(2 * r, n)); y = list(range(n))
    N = r * (q - 2) + n - r - 1
    signs = [-1] * r + [1] * r
    T1 = {}; T2 = {}
    for k in range(1, n + 2, 2):
        hN1 = hcomp(N + 1 - k, A + B, signs, nv, q); hN = hcomp(N - k, A + B, signs, nv, q)
        addto(T1, mul(hN1, elem(k, y, nv), q))
        addto(T2, mul(hN1, elem(k - 1, y, nv), q))
        addto(T2, mul(hN, elem(k, y, nv), q), -1)
    # z*T1 monomials: in n+1 letters, z exponent 1; zeros = zeros among y; heavy = exps q-1
    okT1 = all(sum(1 for e in m if e == 0) <= sum(1 for e in m if e == q - 1) for m in T1)
    # G_r(A;B) = x_A^{q-2} e_{n-r-1}(y \ B)
    G = {}
    base = {i: q - 2 for i in A}
    for S in itertools.combinations(A + P, n - r - 1):
        ex = dict(base)
        for i in S: ex[i] = ex.get(i, 0) + 1
        if max(ex.values()) < q: add(G, mono(nv, ex), 1)
    const = (2 ** (r + 1)) * ((-1) ** n)
    diff = dict(T2); addto(diff, G, -const)
    return okT1, len(T1), len(diff) == 0, len(T2), len(G)

def checkR(n, q):
    # parent (2,1)(n+1): letters y_0..y_{n-1}, z = index n; j = 0, l = 1, P = 2..n-1
    nv = n + 1; Y = list(range(n + 1)); j, l, z = 0, 1, n; P = list(range(2, n)); yl = [i for i in range(n) if i != l]
    M = 2 * q + n - 8
    Om = {}
    for k in range(1, n + 2, 2):
        addto(Om, mul(elem(k, Y, nv), hcomp(M - k, [j, z, l], [-1, -1, 1], nv, q), q))
    Psi = {}; addto(Psi, Om, (-1) ** n)
    def psi(a, b):  # y_a^{q-2} e_{n-2}(Y \ b)
        return mul({mono(nv, {a: q - 2}): 1}, elem(n - 2, [i for i in Y if i != b], nv), q)
    addto(Psi, mul({mono(nv, {z: q - 4}): 1}, psi(j, l), q), -1)
    addto(Psi, mul({mono(nv, {j: q - 4}): 1}, psi(z, l), q), -1)
    phi = mul({mono(nv, {j: q - 2, z: q - 2}): 1}, elem(n - 4, yl, nv), q)
    addto(Psi, phi, -1)
    rest = {m: c for m, c in Psi.items() if m[z] <= q - 2}
    bad = [m for m in rest if sum(1 for e in m if e == 0) > sum(1 for e in m if e == q - 1) + 1]
    return len(bad) == 0, len(rest), len(phi)

def checkZ(m, r, q):
    nv = m; A = list(range(r)); E = list(range(r, 2 * r - 1)); P = list(range(2 * r - 1, m)); y = list(range(m))
    M = r * (q - 1) + len(P) - 1
    signs = [-1] * r + [1] * (r - 1)
    S = {}
    for k in range(1, m + 1, 2):
        addto(S, mul(elem(k, y, nv), hcomp(M - k, A + E, signs, nv, q), q))
    tgt = {}
    c = ((-1) ** (len(P) - 1)) * (2 ** r)
    for w in P:
        add(tgt, mono(nv, dict([(i, q - 1) for i in A] + [(p, 1) for p in P if p != w])), c)
    diff = dict(S); addto(diff, tgt, -1)
    def inL(mm):
        z0 = sum(1 for e in mm if e == 0); hv = sum(1 for e in mm if e == q - 1)
        return z0 <= hv and z0 <= r - 1
    return all(inL(mm) for mm in diff), len(S)

# (C) dictionary counts
def Ipoly(d, deg):  # I_d(2x) = sum_a x^{2a+d}/(a!(a+d)!)
    p = [Fraction(0)] * (deg + 1)
    a = 0
    while 2 * a + d <= deg:
        p[2 * a + d] += Fraction(1, factorial(a) * factorial(a + d)); a += 1
    return p
def pmul(a, b, deg):
    c = [Fraction(0)] * (deg + 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for jj, yv in enumerate(b):
            if i + jj > deg: break
            c[i + jj] += x * yv
    return c
def W(mu, n, q):
    h = (q - 1) // 2
    if len(mu) > h: return 0
    p = [Fraction(1, factorial(i)) for i in range(n + 1)]
    for d in mu: p = pmul(p, Ipoly(d, n), n)
    for _ in range(h - len(mu)): p = pmul(p, Ipoly(0, n), n)
    v = p[n] * factorial(n); assert v.denominator == 1
    return int(v)
def norm(m): return tuple(sorted([x for x in m if x > 0], reverse=True))
def rows(mu, n, q):
    l = len(mu); out = []
    for i in range(l):
        c = list(mu); c[i] -= 1; out.append(norm(c))
    out.append(mu)
    out += [norm(list(mu) + [1])] * (q - 2 * l - 1)
    for i in range(l):
        c = list(mu); c[l - 1 - i] += 1; out.append(norm(c))
    assert len(out) == q
    return out
def checkC(q, top=10):
    vis = set(); st = [((), top)]; bad = 0; cnt = 0
    while st:
        mu, n = st.pop()
        if (mu, n) in vis or n == 0: vis.add((mu, n)); continue
        vis.add((mu, n))
        ch = rows(mu, n, q)
        lhs = W(mu, n, q); rhs = sum(W(c, n - 1, q) for c in ch); cnt += 1
        if lhs != rhs: bad += 1; print('  MISMATCH', mu, n, lhs, rhs)
        for c in set(ch):
            if sum(c) <= n - 1: st.append((c, n - 1))
    return cnt, bad, len(vis), W((), top, q)

if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'T':
        for (r, n, q) in [(2, 5, 9), (2, 6, 9), (2, 7, 9), (2, 8, 9), (3, 6, 9), (3, 8, 9), (2, 5, 27), (2, 6, 27)]:
            print('T r=%d n=%d q=%d  zT1 in N0: %s (#%d)  T2 == 2^(r+1)(-1)^n G: %s (#T2 %d, #G %d)' % ((r, n, q) + checkT(r, n, q)), flush=True)
    if what == 'R':
        for (n, q) in [(5, 9), (6, 9), (7, 9), (5, 27), (6, 27)]:
            print('R n=%d q=%d  Psi - z^(q-2)phi in Mon: %s (#rest %d, #phi %d)' % ((n, q) + checkR(n, q)), flush=True)
    if what == 'Z':
        for (m, r, q) in [(5, 2, 9), (6, 2, 9), (7, 3, 9), (6, 3, 9), (5, 2, 27), (7, 3, 27)]:
            print('Z m=%d r=%d q=%d  identity mod box+L_{r-1}: %s (#%d)' % ((m, r, q) + checkZ(m, r, q)), flush=True)
    if what == 'C':
        for q in (9, 27, 81, 243):
            print('C q=%d  cells checked %d, mismatches %d, visited %d, W_empty(10) = %d' % ((q,) + checkC(q)), flush=True)
    print('FIN-OK', what)
