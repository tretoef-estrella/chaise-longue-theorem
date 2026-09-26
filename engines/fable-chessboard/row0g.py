# mission 13, PART B / F: the row-0 lemma, exact gate over F_3 (pure Python, no Groebner).
# m letters (the child (1)(m) = row 0 of (1,1)(m+1)); heavy A (|A| = r), absent E (|E| = r-1), P = rest.
# Odd_M := sum_{k odd} e_k(y) h_{M-k}(-A, E), M = r(q-1) + m - 2r.  Claim: Odd_M == (-1)^{|P|-1} 2^r x_A^{q-1} e_{|P|-1}(P)
#   modulo box + (layer monomials with |A'| <= r-1, i.e. #zeros <= #(q-1)-exponents and #zeros <= r-1).
# Then: the classes T_A(B) = x_A^{q-1} x_{R\B} (|B| = r) modulo (e_odd)+box+lower layers are spanned by relations
#   sum_{w in R\E} T_A(E+w); rank of that system over F_3 decides whether the |A| = r layer is reached.
import itertools, sys
def hD(D, L, sgn, q, V):
    out = {}
    def rec(i, rem, ex):
        if i == len(L)-1:
            if rem < q:
                e = ex+[rem]; t = [0]*V; s = 0
                for j, v in zip(L, e):
                    t[j] = v
                    if sgn[j] < 0: s += v
                out[tuple(t)] = (-1)**s % 3
            return
        for k in range(0, min(rem, q-1)+1): rec(i+1, rem-k, ex+[k])
    if D >= 0 and L: rec(0, D, [])
    if not L and D == 0: out[tuple([0]*V)] = 1
    return out
def mul(p1, p2, q):
    out = {}
    for e1, c1 in p1.items():
        for e2, c2 in p2.items():
            e = tuple(a+b for a, b in zip(e1, e2))
            if max(e) >= q: continue
            out[e] = (out.get(e, 0)+c1*c2) % 3
    return {k: v for k, v in out.items() if v}
def ek(k, V):
    out = {}
    for S in itertools.combinations(range(V), k):
        t = [0]*V
        for j in S: t[j] = 1
        out[tuple(t)] = 1
    return out
def gate(m, r, q):
    A = list(range(r)); E = list(range(r, 2*r-1)); P = list(range(2*r-1, m))
    sgn = {j: -1 for j in A}; sgn.update({j: 1 for j in E})
    M = r*(q-1)+m-2*r
    odd = {}
    for k in range(1, m+1, 2):
        pr = mul(hD(M-k, A+E, sgn, q, m), ek(k, m), q)
        for e, c in pr.items(): odd[e] = (odd.get(e, 0)+c) % 3
    odd = {e: c for e, c in odd.items() if c}
    def lower(e):
        z0 = sum(1 for x in e if x == 0); zq = sum(1 for x in e if x == q-1)
        return z0 <= zq and z0 <= r-1
    red = {e: c for e, c in odd.items() if not lower(e)}
    c0 = ((-1)**(len(P)-1) * 2**r) % 3
    want = {}
    for S in itertools.combinations(P, len(P)-1):
        t = [0]*m
        for j in A: t[j] = q-1
        for j in S: t[j] = 1
        want[tuple(t)] = c0
    return red == want
def rank_mod3(rows, ncols):
    rows = [list(r) for r in rows]; rk = 0; col = 0
    for col in range(ncols):
        piv = None
        for i in range(rk, len(rows)):
            if rows[i][col] % 3: piv = i; break
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = 1 if rows[rk][col] % 3 == 1 else 2
        rows[rk] = [(x*inv) % 3 for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % 3:
                f = rows[i][col]; rows[i] = [(x-f*y) % 3 for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk
def incid(v, r):   # rows: (r-1)-subsets E of R (|R| = v); cols: r-subsets B; entry 1 iff E subset B
    Bs = list(itertools.combinations(range(v), r)); Es = list(itertools.combinations(range(v), r-1))
    rows = [[1 if set(Ee) <= set(B) else 0 for B in Bs] for Ee in Es]
    return rank_mod3(rows, len(Bs)), len(Bs)
mode = sys.argv[1]
if mode == 'gate':
    for (m, r, q) in [(5, 2, 9), (5, 2, 27), (5, 2, 81), (6, 2, 9), (6, 2, 27), (7, 2, 9), (7, 3, 9), (7, 3, 27), (8, 3, 9), (6, 3, 9), (9, 4, 9)]:
        print("gate m=%d r=%d q=%d: Odd_M == c x_A^(q-1) e_(|P|-1)(P) mod box+lower layers:" % (m, r, q), gate(m, r, q), flush=True)
else:
    for r in range(1, 7):
        for n in range(2*r+1, 2*r+7):
            v = n-1-r
            if v < r: continue
            rk, nc = incid(v, r)
            print("r=%d n=%d (f=%d) v=|R|=%d: rank W_{r-1,r}(v) over F_3 = %d of %d columns -> floor-%d layer %s" % (r, n, n-2, v, rk, nc, r, "REACHED" if rk == nc else "NOT reached"))
