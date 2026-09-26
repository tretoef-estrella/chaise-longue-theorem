# gam14.py — Fable, MISION 14 (2026-09-23). Exact gates over F_3 mod box, pure Python, real letters.
# Reuses the auditor's grepy_verif.py (add, mul, addto, elem, hcomp, mono).
# Gamma^{(s)}(A;B) on the letter set Y is computed FROM THE DEFINITION:
#   [t^D] E_Y(-t) H(t) = sum_k (-1)^k e_k(Y) h_{D-k}(-x_A, x_B),  D = |A|(q-1) + |P| + 1 - s,  P = Y \ (A u B).
import sys, itertools
from grepy_verif import add, mul, addto, elem, hcomp, mono

HC = {}
def h(D, A, B, nv, q):
    key = (D, tuple(A), tuple(B), nv, q)
    if key not in HC:
        HC[key] = hcomp(D, list(A) + list(B), [-1] * len(A) + [1] * len(B), nv, q) if D >= 0 else {}
    return HC[key]

def scal(p, c):
    out = {}
    for m, v in p.items(): add(out, m, v * c)
    return out

def zmul(p, z, e, q):
    out = {}
    for m, v in p.items():
        if m[z] + e < q:
            mm = list(m); mm[z] += e; add(out, tuple(mm), v)
    return out

def gam(s, A, B, Y, nv, q):
    P = [i for i in Y if i not in A and i not in B]
    D = len(A) * (q - 1) + len(P) + 1 - s
    out = {}
    for k in range(0, min(D, len(Y)) + 1):
        addto(out, mul(elem(k, Y, nv), h(D - k, A, B, nv, q), q), (-1) ** k)
    return out

def closed(s, A, B, Y, nv, q):
    # (-1)^D 2^r sum_p e_p(P) h°_{D-p}(x_A), h° = monomials with every exponent in [1, q-1]
    P = [i for i in Y if i not in A and i not in B]; r = len(A)
    D = r * (q - 1) + len(P) + 1 - s
    hz = {}
    for p in range(0, len(P) + 1):
        m = D - p
        hd = {}
        if r == 0:
            if m == 0: hd = {tuple([0] * nv): 1}
        else:
            def rec(i, left, ex):
                if i == r - 1:
                    if 1 <= left <= q - 1:
                        e = ex + [left]; add(hd, mono(nv, dict(zip(A, e))), 1)
                    return
                for x in range(1, min(left, q - 1) + 1): rec(i + 1, left - x, ex + [x])
            if m >= r: rec(0, m, [])
        addto(hz, mul(elem(p, P, nv), hd, q))
    return scal(hz, ((-1) ** D) * (2 ** r))

def eq(a, b):
    d = dict(a); addto(d, b, -1); return len(d) == 0

def oddsum(M, A, B, Y, nv, q):
    out = {}
    for k in range(1, len(Y) + 1, 2):
        addto(out, mul(elem(k, Y, nv), h(M - k, A, B, nv, q), q))
    return out

def trunc(p, z, e):   # drop terms with z-exponent >= e
    return {m: v for m, v in p.items() if m[z] < e}

# ---------- gates ----------
def gate_moves(n, r, w, q):
    """(M-P), (M-B), (M-A), (Z), (Anti) and closed form, on n child letters 0..n-1, z = n."""
    nv = n + 1; z = n; y = list(range(n)); Y1 = list(range(n + 1))
    A = list(range(r)); B = list(range(r, 2 * r + w))
    assert 2 * r + w <= n
    ok = {}
    smax = min(q - 1, 5)
    ok['MP'] = all(eq(gam(s, A, B, Y1, nv, q), addto_ret(gam(s - 1, A, B, y, nv, q), zmul(gam(s, A, B, y, nv, q), z, 1, q), -1)) for s in range(1, smax + 1))
    ok['MB'] = all(eq(gam(s, A, B + [z], Y1, nv, q), gam(s, A, B, y, nv, q)) for s in range(1, smax + 1))
    ma = True
    for s in range(1, smax + 1):
        lhs = gam(s, A + [z], B, Y1, nv, q)
        rhs = gam(s - q + 1, A, B, y, nv, q)
        for i in range(1, q):
            addto(rhs, zmul(gam(s - q + 1 + i, A, B, y, nv, q), z, i, q), -((-1) ** i))
        ma = ma and eq(lhs, rhs)
    ok['MA'] = ma
    ok['Z'] = all(len(gam(s, A, B, y, nv, q)) == 0 for s in (0, -1, -2)) if r >= 1 else True
    ok['closed'] = all(eq(gam(s, A, B, y, nv, q), closed(s, A, B, y, nv, q)) for s in range(1, smax + 1))
    if w == 0:
        an = True
        for s in range(1, smax + 1):
            P = [i for i in y if i not in A and i not in B]; M = r * (q - 1) + len(P) + 1 - s
            rhs = gam(s, A, B, y, nv, q); addto(rhs, gam(s, B, A, y, nv, q), -((-1) ** M))
            an = an and eq(oddsum(M, A, B, y, nv, q), rhs)
        ok['Anti'] = an
    return ok

def addto_ret(a, b, c):
    d = dict(a); addto(d, b, c); return d

def desc(s, a, A, B, y, Y1, z, nv, q):
    """right-hand side of the descent: Gamma^{(s-a)}(A;B u z)(n+1) - sum_{i=1}^a z^{i-1} Gamma^{(s-a+i)}(A;B)(n+1)"""
    out = gam(s - a, A, B + [z], Y1, nv, q)
    for i in range(1, a + 1):
        addto(out, zmul(gam(s - a + i, A, B, Y1, nv, q), z, i - 1, q), -1)
    return out

def gate_A2(n, r, l, q):
    """(A2): z^l Gamma^{(l)}_r(n) == -sum_{i=1}^{l} z^{i-1} Gamma^{(i)}(n+1) mod box (the descent; Gamma^{(0)}(A;B u z) = 0 mod box),
       and the multiplier lemma a*Gamma^{(s)} == -Gamma^{(s-1)} (s <= l) so lower levels lie in the mission's K."""
    nv = n + 1; z = n; y = list(range(n)); Y1 = list(range(n + 1))
    A = list(range(r)); B = list(range(r, 2 * r))
    lhs = zmul(gam(l, A, B, y, nv, q), z, l, q)
    rhs = {}
    for i in range(1, l + 1): addto(rhs, zmul(gam(i, A, B, Y1, nv, q), z, i - 1, q), -1)
    ok1 = eq(lhs, rhs) and eq(lhs, desc(l, l, A, B, y, Y1, z, nv, q))
    ok2 = all(eq(zmul(gam(s, A, B, Y1, nv, q), A[0], 1, q), scal(gam(s - 1, A, B, Y1, nv, q), -1)) for s in range(2, l + 1))
    return ok1, ok2, len(lhs)

def gate_A3(n, r, l, q):
    """(A3): X := C - z^{l+1} C' - Desc(A;B) + (-1)^M Desc(B;A) == z^{l+1} Gamma^{(l+1)}(A;B)(n)  mod box + (z^{l+2}),
       C = z^l sum_{k odd} e_k(y,z) h_{M-k},  C' = sum_{k odd} e_k(y,z) h_{M-1-k},  M = D_n(l),
       Desc(A;B) = -sum_{i=1}^{l} z^{i-1} Gamma^{(i)}(A;B)(n+1) (+ Gamma^{(0)}(A;B u z)(n+1) = 0) = z^l Gamma^{(l)}(A;B)(n) (A2)."""
    nv = n + 1; z = n; y = list(range(n)); Y1 = list(range(n + 1))
    A = list(range(r)); B = list(range(r, 2 * r)); P = [i for i in y if i not in A and i not in B]
    M = r * (q - 1) + len(P) + 1 - l
    C = zmul(oddsum(M, A, B, Y1, nv, q), z, l, q)
    Cp = zmul(oddsum(M - 1, A, B, Y1, nv, q), z, l + 1, q)
    X = dict(C); addto(X, Cp, -1)
    addto(X, desc(l, l, A, B, y, Y1, z, nv, q), -1)
    addto(X, desc(l, l, B, A, y, Y1, z, nv, q), (-1) ** M)
    X = trunc(X, z, l + 2)
    tgt = zmul(gam(l + 1, A, B, y, nv, q), z, l + 1, q)
    return eq(X, tgt), len(tgt), len(C)


def lamw(mu, w): return sum(max(m - w, 0) for m in mu)
def cw(mu, w): return sum(1 for m in mu if m > w)

def gate_NC(n, r, mu, q):
    """general NEW-CLASS certificate: L = |mu|, p = l(mu):
       z^p sum_odd e_k(y,z) h_{M-k} - z^{p+1} sum_odd e_k(y,z) h_{M-1-k} - Desc_{L,p}(A;B) + (-1)^M Desc_{L,p}(B;A) == z^{p+1} Gamma^{(L+1)}(A;B)(n) mod box+(z^{p+2});
       every term of Desc is a parent object of K^G_mu(n+1) (checked: levels <= lam_0, and the M-B term level L-p <= lam_1)."""
    L = sum(mu); p = len(mu)
    assert L - p <= lamw(mu, 1)
    nv = n + 1; z = n; y = list(range(n)); Y1 = list(range(n + 1))
    A = list(range(r)); B = list(range(r, 2 * r)); P = [i for i in y if i not in A and i not in B]
    M = r * (q - 1) + len(P) + 1 - L
    X = zmul(oddsum(M, A, B, Y1, nv, q), z, p, q)
    addto(X, zmul(oddsum(M - 1, A, B, Y1, nv, q), z, p + 1, q), -1)
    addto(X, desc(L, p, A, B, y, Y1, z, nv, q), -1)
    addto(X, desc(L, p, B, A, y, Y1, z, nv, q), (-1) ** M)
    X = trunc(X, z, p + 2)
    tgt = zmul(gam(L + 1, A, B, y, nv, q), z, p + 1, q)
    return eq(X, tgt), len(tgt)

def gate_raise(n, r, w, mu, q):
    """RAISE certificate: Pi = Gamma^{(s')}(A u z; B)(n+1), s' = lam_{w-1}(mu); subtract the lower z-terms, each written by its
       descent certificate (parent objects only; inequalities asserted); the rest mod box + (z^{i*+1}) must be -(-z)^{i*} Gamma^{(t)}(n),
       t = lam_w(mu)+1, i* = q - c_{w-1}(mu)."""
    l = len(mu); assert w >= 1 and 2 * l <= q - 1
    sp = lamw(mu, w - 1); t = lamw(mu, w) + 1; istar = q - cw(mu, w - 1)
    assert t <= sp
    nv = n + 1; z = n; y = list(range(n)); Y1 = list(range(n + 1))
    A = list(range(r)); B = list(range(r, 2 * r + w)); assert 2 * r + w <= n
    X = gam(sp, A + [z], B, Y1, nv, q)
    for i in range(0, istar):
        u = sp - q + 1 + i
        if u <= 0: continue
        assert u <= lamw(mu, w) and u - i <= lamw(mu, w + 1)
        c = 1 if i == 0 else -((-1) ** i)
        addto(X, desc(u, i, A, B, y, Y1, z, nv, q), -c)
    X = trunc(X, z, istar + 1)
    tgt = scal(zmul(gam(t, A, B, y, nv, q), z, istar, q), -((-1) ** istar))
    return eq(X, tgt), istar, len(tgt)

if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'moves':
        cells = [(4, 1, 0, 9), (5, 2, 0, 9), (6, 2, 0, 9), (6, 1, 1, 9), (6, 1, 2, 9), (7, 1, 2, 9), (7, 2, 0, 9), (5, 0, 2, 9), (6, 0, 3, 9),
                 (4, 1, 1, 27), (5, 1, 1, 27), (4, 2, 0, 27), (4, 0, 2, 27)]
        for c in cells:
            HC.clear()
            print('moves n=%d r=%d w=%d q=%d' % c, gate_moves(*c), flush=True)
    if what == 'A2':
        cells = [(4, 2, 2, 9), (5, 2, 2, 9), (6, 2, 3, 9), (6, 3, 3, 9), (7, 2, 3, 9), (8, 2, 3, 9), (8, 2, 4, 9),
                 (4, 2, 2, 27), (5, 2, 3, 27), (6, 2, 3, 27)]
        for c in cells:
            HC.clear()
            print('A2 n=%d r=%d l=%d q=%d  descent exact: %s  multiplier lemma: %s  (#terms %d)' % (c + gate_A2(*c)), flush=True)
    if what == 'A3':
        cells = [(4, 2, 1, 9), (5, 2, 1, 9), (5, 2, 2, 9), (6, 2, 2, 9), (6, 3, 2, 9), (7, 2, 2, 9), (8, 2, 2, 9), (7, 2, 3, 9),
                 (4, 2, 2, 27), (5, 2, 2, 27)]
        for c in cells:
            HC.clear()
            print('A3 n=%d r=%d l=%d q=%d  certificate == z^(l+1) Gamma^(l+1): %s  (#target %d, #C %d)' % (c + gate_A3(*c)), flush=True)
    if what == 'NC':
        cells = [(5, 2, (2,), 9), (6, 1, (3,), 9), (6, 2, (2, 1), 9), (7, 2, (2, 2), 9), (7, 2, (3, 1), 9), (7, 1, (2, 1, 1), 9),
                 (5, 2, (2,), 27), (5, 2, (2, 1), 27)]
        for c in cells:
            HC.clear()
            print('NC n=%d r=%d mu=%s q=%d  certificate == z^(l+1) Gamma^(|mu|+1): %s (#target %d)' % (c + gate_NC(*c)), flush=True)
    if what == 'raise':
        cells = [(5, 0, 1, (1, 1), 9), (5, 1, 1, (1, 1), 9), (6, 1, 1, (1, 1), 9), (6, 1, 1, (2, 1), 9), (6, 1, 1, (2, 2), 9), (6, 1, 2, (2, 2), 9),
                 (6, 0, 2, (3, 1), 9), (6, 1, 2, (3, 1), 9), (7, 1, 1, (2, 1, 1), 9), (7, 2, 1, (1, 1), 9), (6, 1, 1, (3, 2), 9),
                 (5, 1, 1, (1, 1), 27), (5, 1, 1, (2, 2), 27), (5, 0, 2, (3, 1), 27)]
        for c in cells:
            HC.clear()
            print('RAISE n=%d r=%d w=%d mu=%s q=%d  certificate: %s (row i* = q-%d, #target %d)' % (c + (lambda o: (o[0], c[4] - o[1], o[2]))(gate_raise(*c))), flush=True)
    if what == 'E':
        HC.clear(); print('E RAISE parent (1,1)(9) -> (2,1)(8), r=2 w=1:', gate_raise(8, 2, 1, (1, 1), 9), flush=True)
        HC.clear(); print('E RAISE parent (2,1)(9) -> (2,2)(8), r=1 w=1:', gate_raise(8, 1, 1, (2, 1), 9), flush=True)
        HC.clear(); print('E NC parent (2,1)(9) -> (2,1,1)(8), r=2:', gate_NC(8, 2, (2, 1), 9), flush=True)
        HC.clear(); print('E NC parent (1,1,1)(9) -> (1^4)(8), r=2:', gate_NC(8, 2, (1, 1, 1), 9), flush=True)
        HC.clear(); print('E NC parent (2)(10) -> (2,1)(9), r=2:', gate_NC(9, 2, (2,), 9), flush=True)
    print('FIN-OK', what)
