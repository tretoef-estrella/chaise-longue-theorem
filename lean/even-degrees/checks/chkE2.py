# Piece E2 checks (q_even_count.md): the count for even m and the upper bound.
# K[G] = K[t_1..t_d]/(t_i^m - 1), d = 2k+1, I = (psi_J : J a matching of {0..2k+1}).
# (A) Qe_k(m) by the explicit sum, by the recursion 1 + sum_c C(N,2c) Q_{k-c}(m-1), by brute force
#     (closed tuples of Z/m minus 0 under negation, fixed point m/2 used an even number of times),
#     and against the table of the paper (v11, section 9.1).
# (B) |Gamma| by evaluating every psi_J at every point of mu_m^d over F_P, P = 1 mod m.
# (C) rank of I over F_p for every prime p | m (the upper bound: <= Qe) and over F_P (= |Gamma| = Qe).
# (D) controls: one matching removed from the family; the odd formula Q_k(m) read at an even m.
#     (The control of piece 28, t+1 in place of t-1, cannot fire for even m: t -> -t is an automorphism of K[G]
#     that carries one ideal to the other. It was run first, was silent in 7 cells of 7, and was replaced.)
import itertools, sys, numpy as np
from math import factorial, comb
from collections import Counter

def matchings_list(L):
    if not L: yield []; return
    a = L[0]
    for b in L[1:]:
        rest = [x for x in L if x not in (a, b)]
        for M in matchings_list(rest): yield [(a, b)] + M

def comps(total, parts):
    if parts == 0:
        if total == 0: yield ()
        return
    for x in range(total + 1):
        for r in comps(total - x, parts - 1): yield (x,) + r

def Qodd(k, q):                     # TheoremB.Qk: sum over b in N^h, sum b = k+1, of N!/prod (b!)^2
    h = (q - 1) // 2; N = 2*k + 2; s = 0
    for b in comps(k + 1, h):
        den = 1
        for x in b: den *= factorial(x)**2
        assert factorial(N) % den == 0
        s += factorial(N) // den
    return s

def Qe_explicit(k, m):              # N! [x^N] cosh(x) I_0(2x)^h, h = (m-2)/2
    h = (m - 2) // 2; N = 2*k + 2; s = 0
    for c in range(k + 2):
        for b in comps(k + 1 - c, h):
            den = factorial(2*c)
            for x in b: den *= factorial(x)**2
            assert factorial(N) % den == 0
            s += factorial(N) // den
    return s

def Qe_rec(k, m):
    N = 2*k + 2
    return 1 + sum(comb(N, 2*c) * Qodd(k - c, m - 1) for c in range(k + 1))

def Qe_brute(k, m):
    o = m // 2; n = 0
    for g in itertools.product(range(1, m), repeat=2*k + 2):
        C = Counter(g)
        if C[o] % 2 == 0 and all(C[x] == C[(-x) % m] for x in C): n += 1
    return n

TABLE = {4: [19, 141, 1107, 8953, 73789], 6: [61, 1001, 18733, 375745, 7858225],
         8: [127, 3301, 103279, 3595177, 133789789], 10: [217, 7761, 345465, 17605249, 980612161],
         12: [331, 15101, 876331, 59415961, 4481629021], 16: [631, 41301, 3529863, 361612105, 42214788925]}

def polymul(P, Q, m, p):
    R = {}
    for e1, c1 in P.items():
        for e2, c2 in Q.items():
            e = tuple((x + y) % m for x, y in zip(e1, e2)); R[e] = (R.get(e, 0) + c1 * c2) % p
    return {e: c for e, c in R.items() if c}

def psi(J, m, d, p, sign=-1):
    def t(a):
        e = [0]*d; e[a-1] = 1; return tuple(e)
    P = {(0,)*d: 1}
    for (a, b) in J:
        P = polymul(P, {t(b): 1, (0,)*d: sign % p}, m, p)
        if a > 0:
            phi = {}
            for s in range(m):
                e = [0]*d; e[a-1] = s; e[b-1] = s; phi[tuple(e)] = 1
            P = polymul(P, phi, m, p)
    return P

def rank_mod(A, p):
    A = A % p; r = 0; nrows, ncols = A.shape
    for c in range(ncols):
        nzc = np.nonzero(A[r:, c])[0]
        if len(nzc) == 0: continue
        piv = r + int(nzc[0])
        if piv != r: A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p); A[r] = (A[r] * inv) % p
        col = A[:, c].copy(); col[r] = 0
        nz = np.nonzero(col)[0]
        for i0 in range(0, len(nz), 2000):          # in blocks, to bound the temporary
            blk = nz[i0:i0 + 2000]
            A[blk] = (A[blk] - np.outer(col[blk], A[r])) % p
        r += 1
        if r == nrows: break
    return r

def ideal_rank(m, k, p, sign=-1, drop=None):
    d = 2*k + 1; cols = list(itertools.product(range(m), repeat=d)); idx = {e: i for i, e in enumerate(cols)}
    Js = list(matchings_list(list(range(2*k + 2))))
    if drop is not None: Js = Js[:drop] + Js[drop+1:]
    A = np.zeros((len(Js) * len(cols), len(cols)), dtype=np.int32); r = 0
    for J in Js:
        P = psi(J, m, d, p, sign)
        for nu in cols:
            for e, c in P.items(): A[r, idx[tuple((x + y) % m for x, y in zip(e, nu))]] = c
            r += 1
    return rank_mod(A, p)

def primes_of(m): return [f for f in range(2, m + 1) if m % f == 0 and all(f % e for e in range(2, f))]

def roots(m, P):
    for g in range(2, P):
        z = pow(g, (P - 1)//m, P)
        if all(pow(z, j, P) != 1 for j in range(1, m)): return [pow(z, j, P) for j in range(m)]

def gamma_eval(m, k, P):
    d = 2*k + 1; mu = roots(m, P); cnt = 0
    Js = list(matchings_list(list(range(2*k + 2))))
    phi = {u: sum(pow(u, s, P) for s in range(m)) % P for u in range(P)}
    for a in itertools.product(mu, repeat=d):
        av = (None,) + a
        for J in Js:
            val = 1
            for (x, y) in J:
                val = val * (av[y] - 1) % P
                if x > 0: val = val * phi[av[x]*av[y] % P] % P
                if not val: break
            if val: cnt += 1; break
    return cnt

good = {2: 3, 4: 5, 6: 7, 8: 17, 10: 11, 12: 13}
checks = bad = 0

print("(A) the count")
for m, vals in TABLE.items():
    for k, v in enumerate(vals, start=1):
        e = Qe_explicit(k, m); r = Qe_rec(k, m); checks += 1; ok = (e == r == v); bad += (not ok)
        if not ok: print(f"  FAIL m={m} k={k}: explicit {e} recursion {r} table {v}")
print(f"  explicit sum = recursion = table of the paper in {sum(len(v) for v in TABLE.values())} cells")
for (m, k) in [(2,1), (2,2), (4,1), (4,2), (4,3), (6,1), (6,2), (8,1), (8,2), (10,1), (10,2), (12,1)]:
    b = Qe_brute(k, m); e = Qe_explicit(k, m); r = Qe_rec(k, m); checks += 1; ok = (b == e == r); bad += (not ok)
    print(f"  m={m} k={k}: brute {b} explicit {e} recursion {r} {'OK' if ok else 'FAIL'}", flush=True)
for (m, k) in [(4,1), (6,1), (8,2), (12,3)]:
    checks += 1; ok = (Qe_explicit(1, m) == 3*m*m - 9*m + 7); bad += (not ok)
print("  Q_1(m) = 3m^2 - 9m + 7 at m = 4, 6, 8, 12:", all(Qe_explicit(1, m) == 3*m*m - 9*m + 7 for m in (4, 6, 8, 12)))

print("(B) the points, by evaluation over F_P")
for (m, k) in [(2,1), (2,2), (4,1), (6,1), (8,1), (10,1), (12,1), (4,2), (6,2), (8,2), (4,3)]:
    P = good[m]; G = gamma_eval(m, k, P); Q = Qe_explicit(k, m); checks += 1; ok = (G == Q); bad += (not ok)
    print(f"  m={m} k={k}: |Gamma| over F_{P} = {G}, Qe = {Q} {'OK' if ok else 'FAIL'}", flush=True)

print("(C) the ranks")
for (m, k) in [(2,1), (4,1), (6,1), (8,1), (10,1), (2,2), (4,2)]:
    Q = Qe_explicit(k, m)
    rp = {p: ideal_rank(m, k, p) for p in primes_of(m)}
    P = good[m]; rP = ideal_rank(m, k, P)
    ok = all(v <= Q for v in rp.values()) and rP == Q; checks += 1; bad += (not ok)
    eq = all(v == Q for v in rp.values())
    ctrl = ideal_rank(m, k, P, drop=0)
    print(f"  m={m} k={k}: Qe={Q} rank over F_p (p|m) {rp} ({'all equal' if eq else 'some strictly smaller'}) | rank over F_{P}={rP} "
          f"{'OK' if ok else 'FAIL'} | control (one matching removed) rank={ctrl} {'fires' if ctrl != Q else 'SILENT'}", flush=True)

print("(D) control: the odd formula read at an even m")
fires = sum(1 for m in TABLE for k in range(1, 6) if Qodd(k, m) != TABLE[m][k-1])
print(f"  Q_k(m) (no fixed point) differs from the table in {fires} of 30 cells")
print(f"checks {checks}, failures {bad}")
print("FIN-OK")
