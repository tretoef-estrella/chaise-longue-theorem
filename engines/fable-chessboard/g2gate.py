# E1 (mission 13): exact gate of the pencil closed forms of 0.1, over F_3, mod box.
# Letters: A (heavy, sign -), B (absent, sign +), |A|=|B|=r; P formal: basis e_p(P), |P| = n-2r.
# Poly = dict {(exps tuple over the 2r letters, p): coeff mod 3}; exponents >= q dropped (box).
import itertools, sys
def hD(D, r, q):
    # complete homogeneous h_D(-A, B) mod box, as dict exps->coeff
    out = {}
    L = 2*r
    def rec(i, rem, ex):
        if i == L-1:
            if rem < q:
                e = ex + [rem]
                s = sum(e[:r]) % 2
                out[tuple(e)] = (-1)**s % 3
            return
        for k in range(0, min(rem, q-1)+1):
            rec(i+1, rem-k, ex+[k])
    if D >= 0: rec(0, D, [])
    return out
def ek_y(k, r, nP):
    # e_k(y) = sum_{S subset letters} x_S e_{k-|S|}(P)
    out = {}
    L = 2*r
    for s in range(0, L+1):
        p = k - s
        if p < 0 or p > nP: continue
        for S in itertools.combinations(range(L), s):
            ex = [0]*L
            for i in S: ex[i] = 1
            out[(tuple(ex), p)] = 1
    return out
def mul_h_e(h, e, q):
    out = {}
    for (ex2, p), c2 in e.items():
        for ex1, c1 in h.items():
            ex = tuple(a+b for a, b in zip(ex1, ex2))
            if max(ex) >= q: continue
            key = (ex, p)
            out[key] = (out.get(key, 0) + c1*c2) % 3
    return {k: v for k, v in out.items() if v}
def add(*ps):
    out = {}
    for sgn, p in ps:
        for k, v in p.items():
            out[k] = (out.get(k, 0) + sgn*v) % 3
    return {k: v for k, v in out.items() if v}
def G(r, n, q, heavy):  # G_r(heavy; other) = x_H^{q-2} e_{n-r-1}(H u P)
    L = 2*r; nP = n-2*r; out = {}
    idx = list(range(r)) if heavy == 'A' else list(range(r, 2*r))
    for s in range(0, r+1):
        p = n-r-1-s
        if p < 0 or p > nP: continue
        for S in itertools.combinations(idx, s):
            ex = [0]*L
            for i in idx: ex[i] = q-2
            for i in S: ex[i] += 1
            out[(tuple(ex), p)] = 1
    return out
def mono(ex, p, c=1): return {(tuple(ex), p): c % 3}
def run(r, n, q):
    nP = n-2*r; N = r*(q-2)+n-r-1; L = 2*r
    top = {}; sh = {}; od = {}
    for k in range(0, n+1):
        e = ek_y(k, r, nP)
        if k % 2 == 1:
            top = add((1, top), (1, mul_h_e(hD(N+1-k, r, q), e, q)))
            od = add((1, od), (1, mul_h_e(hD(N-k, r, q), e, q)))
        else:
            sh = add((1, sh), (1, mul_h_e(hD(N-k, r, q), e, q)))
    s = (-1)**n; tr = pow(2, r, 3)
    GA = G(r, n, q, 'A'); GB = G(r, n, q, 'B')
    topF = add((-tr, mono([0]*r+[q-1]*r, nP)), (tr*s, mono([q-1]*r+[0]*r, nP)))
    shF = add((-tr, GB), (tr*s, GA))
    odF = add((-tr, GB), (-tr*s, GA))
    ok = (top == topF, sh == shF, od == odF)
    diff = add((1, sh), (-1, od))
    ok2 = diff == add((pow(2, r+1, 3)*s, GA),)
    return ok + (ok2, len(top), len(sh), len(od))
cells = []
QS = [int(x) for x in sys.argv[1].split(',')]
for q in QS:
    for r in (1, 2, 3):
        if q >= 27 and r == 3: continue
        for n in range(max(2*r, 3), 10):
            if q == 81 and n > 6: continue
            cells.append((r, n, q))
bad = 0
for (r, n, q) in cells:
    res = run(r, n, q)
    print("r=%d n=%d q=%d  Top,Shadow,Odd closed forms:" % (r, n, q), res[:3], " Shadow-Odd = 2^(r+1)(-1)^n G_r:", res[3], " sizes", res[4:])
    if not all(res[:4]): bad += 1
print("CELLS", len(cells), "FAILED", bad)
