# regla274 — gate of (S) over F_p for q = p^v (p odd): dim_{F_p}(D_J : J)C  vs  Q_k(q).
# Calibration at p=3 against the paper: (1,3)=6, (2,3)=20, (1,9)=168. Then p=5,7 (outside the paper's claim).
# Grepy el Auditor, 2026-09-24. Degree-by-degree rank mod p; C = F_p[y]/(y_i^{q-1}).
import sys, itertools, numpy as np
from math import factorial
from fractions import Fraction

def matchings(pts):
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        b = pts[i]; rest = pts[1:i] + pts[i+1:]
        for m in matchings(rest): yield [(a, b)] + m

def Q(k, q):  # number of N-tuples in F_q^x closed under negation, N=2k+2: N![x^N] I0(2x)^h
    N = 2*k+2; h = (q-1)//2
    I0 = [Fraction(0)]*(N+1)
    for b in range(N//2+1): I0[2*b] = Fraction(1, factorial(b)**2)
    poly = [Fraction(1)] + [Fraction(0)]*N
    for _ in range(h):
        new = [Fraction(0)]*(N+1)
        for i, a in enumerate(poly):
            if a:
                for j, c in enumerate(I0):
                    if i+j <= N and c: new[i+j] += a*c
        poly = new
    return int(poly[N]*factorial(N))

def run(k, p, q):
    nv = 2*k+1; e = q-2  # exponents 0..q-2 in C
    # D(a,b) = sum_{u=0}^{q-2} (-1)^u a^u b^{q-2-u}
    def D(i, j):
        pol = {}
        for u in range(q-1):
            mono = [0]*nv; mono[i] += u; mono[j] += q-2-u
            pol[tuple(mono)] = (-1)**u % p
        return pol
    def mul(A, B):
        out = {}
        for m1, c1 in A.items():
            for m2, c2 in B.items():
                m = tuple(x+y for x, y in zip(m1, m2))
                if max(m) > e: continue
                out[m] = (out.get(m, 0) + c1*c2) % p
        return {m: c for m, c in out.items() if c}
    gens = []
    for J in matchings(list(range(nv+1))):  # points 0..2k+1, y-index = point-1, drop pair with 0
        pol = {tuple([0]*nv): 1}
        for (a, b) in J:
            if a == 0: continue
            pol = mul(pol, D(a-1, b-1))
        gens.append(pol)
    d0 = k*(q-2)
    monos_by_deg = {}
    for m in itertools.product(range(e+1), repeat=nv):
        monos_by_deg.setdefault(sum(m), []).append(m)
    total = 0
    for d in range(d0, nv*e+1):
        cols = monos_by_deg.get(d, [])
        if not cols: continue
        idx = {m: i for i, m in enumerate(cols)}
        rows = []
        for g in gens:
            for s in monos_by_deg.get(d-d0, []):
                v = np.zeros(len(cols), dtype=np.int64)
                for m, c in g.items():
                    mm = tuple(x+y for x, y in zip(m, s))
                    if max(mm) <= e: v[idx[mm]] = (v[idx[mm]] + c) % p
                if v.any(): rows.append(v)
        if not rows: continue
        M = np.array(rows) % p
        r = 0; nr, nc = M.shape
        for c in range(nc):
            piv = None
            for i in range(r, nr):
                if M[i, c]: piv = i; break
            if piv is None: continue
            M[[r, piv]] = M[[piv, r]]
            inv = pow(int(M[r, c]), p-2, p)
            M[r] = (M[r]*inv) % p
            nz = np.nonzero(M[:, c])[0]
            for i in nz:
                if i != r: M[i] = (M[i] - M[i, c]*M[r]) % p
            r += 1
            if r == nr: break
        total += r
    return total

cells = [(1,3,3),(2,3,3),(1,3,9),(1,5,5),(2,5,5),(1,7,7),(2,7,7),(3,5,5),(1,5,25)]
for (k, p, q) in cells:
    got = run(k, p, q); want = Q(k, q)
    print(f"k={k} p={p} q={q}: dim(D_J)C = {got}   Q_k(q) = {want}   {'OK' if got == want else 'DIFFERS'}", flush=True)
print("FIN-OK", flush=True)
