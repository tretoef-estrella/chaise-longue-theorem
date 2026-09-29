# Piece 28 checks: dim_K (psi_J : J) K[G], K[G] = K[t_1..t_d]/(t_i^m - 1), d = 2k+1.
# (a) for p | m: rank over F_p <= Q_k(m) (the upper bound (6.1)); (b) for a prime P = 1 mod m:
# rank over F_P = #{a in mu_m^d : some psi_J(a) != 0} = Q_k(m) (the count); (c) controls.
import itertools, numpy as np
from collections import Counter

def matchings(n):
    if n == 0: yield []; return
    a = 0
    for b in range(1, n):
        rest = [x for x in range(n) if x not in (a, b)]
        for M in matchings_list(rest): yield [(a, b)] + M
def matchings_list(L):
    if not L: yield []; return
    a = L[0]
    for b in L[1:]:
        rest = [x for x in L if x not in (a, b)]
        for M in matchings_list(rest): yield [(a, b)] + M

def polymul(P, Q, m, p):
    R = {}
    for e1, c1 in P.items():
        for e2, c2 in Q.items():
            e = tuple((x + y) % m for x, y in zip(e1, e2)); R[e] = (R.get(e, 0) + c1 * c2) % p
    return {e: c for e, c in R.items() if c}

def psi(J, m, d, p, sign=-1):
    one = {(0,)*d: 1}
    def t(a):  # t_a, a in 1..d  -> variable a-1
        e = [0]*d; e[a-1] = 1; return tuple(e)
    P = dict(one)
    for (a, b) in J:
        P = polymul(P, {t(b): 1, (0,)*d: sign % p}, m, p)          # (t_b - 1)  [control: t_b + 1]
        if a > 0:
            phi = {}
            for s in range(m):
                e = [0]*d; e[a-1] = s; e[b-1] = s; phi[tuple(e)] = 1
            P = polymul(P, phi, m, p)
    return P

def rank_mod(rows, p):
    A = np.array(rows, dtype=np.int64) % p; r = 0; nrows, ncols = A.shape
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if A[i, c]: piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p); A[r] = (A[r] * inv) % p
        col = A[:, c].copy(); col[r] = 0
        nz = np.nonzero(col)[0]
        if len(nz): A[nz] = (A[nz] - np.outer(col[nz], A[r])) % p
        r += 1
        if r == nrows: break
    return r

def ideal_rank(m, k, p, sign=-1):
    d = 2*k + 1; cols = list(itertools.product(range(m), repeat=d)); idx = {e: i for i, e in enumerate(cols)}
    rows = []
    for J in matchings_list(list(range(2*k + 2))):
        P = psi(J, m, d, p, sign)
        for nu in cols:
            v = [0]*len(cols)
            for e, c in P.items(): v[idx[tuple((x + y) % m for x, y in zip(e, nu))]] = c
            rows.append(v)
    return rank_mod(rows, p)

def Qk(k, m):  # closed tuples in (Z/m minus 0)^{2k+2}
    return sum(1 for g in itertools.product(range(1, m), repeat=2*k+2)
               if all(Counter(g)[x] == Counter(g)[(-x) % m] for x in set(g)))

def gamma_eval(m, k, P):   # count points a in mu_m^d (in F_P) with some psi_J(a) != 0, by evaluation
    d = 2*k + 1; g = next(x for x in range(2, P) if all(pow(x, (P-1)//q, P) != 1 for q in {f for f in range(2, P) if (P-1) % f == 0 and all(f % e for e in range(2, f))}))
    z = pow(g, (P-1)//m, P); mu = [pow(z, j, P) for j in range(m)]
    cnt = 0
    Js = list(matchings_list(list(range(2*k + 2))))
    for a in itertools.product(mu, repeat=d):
        av = (None,) + a
        for J in Js:
            val = 1
            for (x, y) in J:
                val = val * (av[y] - 1) % P
                if x > 0: val = val * sum(pow(av[x]*av[y] % P, s, P) for s in range(m)) % P
            if val: cnt += 1; break
    return cnt

good = {3: 7, 5: 11, 7: 29, 9: 19, 15: 31}
bad = 0; checks = 0
for (m, k) in [(3,1), (5,1), (7,1), (9,1), (3,2)]:
    Q = Qk(k, m)
    rp = {p: ideal_rank(m, k, p) for p in sorted({f for f in range(2, m+1) if m % f == 0 and all(f % e for e in range(2, f))})}
    P = good[m]; rP = ideal_rank(m, k, P); G = gamma_eval(m, k, P)
    ok = all(v <= Q for v in rp.values()) and rP == G == Q
    checks += 1; bad += (not ok)
    ctrl = ideal_rank(m, k, P, sign=+1)
    print(f"m={m} k={k}: Q={Q} rank over F_p (p|m) {rp} | rank over F_{P}={rP} points={G} {'OK' if ok else 'FAIL'} | control (t+1) rank={ctrl} {'fires' if ctrl != Q else 'SILENT'}", flush=True)
P = good[15]; G = gamma_eval(15, 1, P); Q = Qk(1, 15); checks += 1; bad += (G != Q)
print(f"m=15 k=1: points over F_{P}={G} Q={Q} {'OK' if G == Q else 'FAIL'}")
print(f"checks {checks}, failures {bad}")
