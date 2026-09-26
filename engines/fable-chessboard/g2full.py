# E2 (mission 13): the certificate Phi in the n+1 REAL variables (y_1..y_n, z), over F_3, mod box.
# Phi := z*sum_{k odd} h_{N+1-k}(-A,B) e_k(y,z) - z^2*sum_{k odd} h_{N-k}(-A,B) e_k(y,z),  N = deg G_r.
# Checks: z^1-part is a sum of N_0(n+1) monomials (monomial criterion of the (1) casilla), z^2-part == (-1)^(n+1) 2^(r+1) G_r(A;B).
import itertools, sys
def run(r, n, q):
    V = n+1; zi = n
    A = list(range(r)); B = list(range(r, 2*r))
    N = r*(q-2)+n-r-1
    # h_D(-A,B) as dict over V vars (only letters of A,B)
    def hD(D):
        out = {}
        L = A+B
        def rec(i, rem, ex):
            if i == len(L)-1:
                if rem < q:
                    e = ex+[rem]; s = sum(e[:r]) % 2
                    t = [0]*V
                    for j, v in zip(L, e): t[j] = v
                    out[tuple(t)] = (-1)**s % 3
                return
            for k in range(0, min(rem, q-1)+1): rec(i+1, rem-k, ex+[k])
        if D >= 0: rec(0, D, [])
        return out
    def ek(k, vars_):
        out = {}
        for S in itertools.combinations(vars_, k):
            t = [0]*V
            for j in S: t[j] = 1
            out[tuple(t)] = 1
        return out
    def mul(p1, p2):
        out = {}
        for e1, c1 in p1.items():
            for e2, c2 in p2.items():
                e = tuple(a+b for a, b in zip(e1, e2))
                if max(e) >= q: continue
                out[e] = (out.get(e, 0)+c1*c2) % 3
        return {k: v for k, v in out.items() if v}
    def add(p, qq, s=1):
        out = dict(p)
        for k, v in qq.items(): out[k] = (out.get(k, 0)+s*v) % 3
        return {k: v for k, v in out.items() if v}
    yz = list(range(V)); z1 = [0]*V; z1[zi] = 1; z2 = [0]*V; z2[zi] = 2
    Phi = {}
    for k in range(1, V+1, 2):
        E = ek(k, yz)
        Phi = add(Phi, mul(mul(hD(N+1-k), E), {tuple(z1): 1}))
        Phi = add(Phi, mul(mul(hD(N-k), E), {tuple(z2): 1}), -1)
    # closed form of G_r(A;B) in the real variables
    P = list(range(2*r, n))
    G = {}
    for S in itertools.combinations(A+P, n-r-1):
        t = [0]*V
        for j in A: t[j] = q-2
        for j in S: t[j] += 1
        t[zi] = 2
        G[tuple(t)] = 1
    c = ((-1)**n * pow(2, r+1, 3)) % 3   # = 2^(r+1)(-1)^n, as gated in E1
    z2part = {e: v for e, v in Phi.items() if e[zi] == 2}
    ok2 = z2part == {e: (c*v) % 3 for e, v in G.items()}
    z1part = {e: v for e, v in Phi.items() if e[zi] == 1}
    def inN0(e):  # monomial in the (1) casilla's N_0(n+1)+box+(x_[n+1]): #zeros <= #(q-1)-exponents
        return sum(1 for x in e if x == 0) <= sum(1 for x in e if x == q-1)
    ok1 = all(inN0(e) for e in z1part)
    other = [e for e in Phi if e[zi] not in (1, 2) and e[zi] < 3]
    return ok1, ok2, len(z1part), len(z2part), len(other)
cells = [(2, 4, 9), (2, 5, 9), (2, 6, 9), (1, 5, 9), (3, 6, 9), (2, 4, 27), (2, 5, 27)]
bad = 0
for (r, n, q) in cells:
    res = run(r, n, q)
    print("r=%d n=%d q=%d: z^1-part in N_0(n+1): %s; z^2-part == 2^(r+1)(-1)^n G_r: %s; sizes z1=%d z2=%d; z^0 terms %d" % ((r, n, q)+res))
    if not (res[0] and res[1] and res[4] == 0): bad += 1
print("CELLS", len(cells), "FAILED", bad)
