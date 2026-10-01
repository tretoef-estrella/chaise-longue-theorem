# Coinvariants of the finite group Z(F_p) on V^{(x)n}, V = F_p[x]/(x^q), against the ring of Theorem A.
# Z(F_p) = { f(e) : f(e) f(-e) = 1, f(0) = 1 }, acting on F_p[x_1..x_n]/(x_i^q) by multiplication by prod f(x_i).
# Grepy, 2026-10-01 (double check of the cold reader's finding P4).
import itertools, sys
def run(p, q, n):
    # elements of Z(F_p): f = 1 + a_1 x + ... + a_{q-1} x^{q-1} with f(x) f(-x) = 1 mod x^q
    def mul(f, g):
        h = [0]*q
        for i, a in enumerate(f):
            if a:
                for j, b in enumerate(g):
                    if i + j < q: h[i+j] = (h[i+j] + a*b) % p
        return h
    Z = []
    for tail in itertools.product(range(p), repeat=q-1):
        f = [1] + list(tail)
        fm = [(c if i % 2 == 0 else (-c) % p) for i, c in enumerate(f)]
        if mul(f, fm) == [1] + [0]*(q-1): Z.append(f)
    mons = list(itertools.product(range(q), repeat=n)); idx = {m: i for i, m in enumerate(mons)}
    D = len(mons)
    def polymul(P, Q):   # dict monomial -> coeff, in the box
        R = {}
        for m1, c1 in P.items():
            for m2, c2 in Q.items():
                m = tuple(a+b for a, b in zip(m1, m2))
                if max(m) < q: R[m] = (R.get(m, 0) + c1*c2) % p
        return {m: c for m, c in R.items() if c}
    rows = []
    for f in Z:
        P = {tuple([0]*n): 1}
        for i in range(n):
            fi = {tuple(j if t == i else 0 for t in range(n)): c for j, c in enumerate(f) if c}
            P = polymul(P, fi)
        P[tuple([0]*n)] = (P.get(tuple([0]*n), 0) - 1) % p      # prod f(x_i) - 1
        P = {m: c for m, c in P.items() if c}
        for m0 in mons:                                         # (g-1) * monomial
            v = {}
            for m, c in P.items():
                mm = tuple(a+b for a, b in zip(m, m0))
                if max(mm) < q: v[idx[mm]] = c
            if v: rows.append(v)
    # rank mod p by sparse elimination
    piv = {}
    for v in rows:
        v = dict(v)
        while v:
            k = min(v)
            if k in piv:
                c = v[k]; w = piv[k]
                for kk, cc in w.items():
                    nv = (v.get(kk, 0) - c*cc) % p
                    if nv: v[kk] = nv
                    else: v.pop(kk, None)
            else:
                inv = pow(v[k], p-2, p); piv[k] = {kk: cc*inv % p for kk, cc in v.items()}; break
    return len(Z), D - len(piv)
for (p, q, n, ring) in [(3,3,3,7), (3,3,4,19), (3,5,3,13), (5,3,3,7), (5,5,3,13)]:
    z, co = run(p, q, n)
    print(f"p={p} q={q} n={n}: |Z(F_p)|={z}  coinvariants of Z(F_p)={co}  ring of Theorem A={ring}", flush=True)
print("FIN-OK")
