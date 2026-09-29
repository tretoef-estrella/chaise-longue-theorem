# Piece 29 checks: for odd m, rank over F_p of the integer matrix of (psi_J : J) equals Q_k(m) for EVERY prime p
# (so R/(psi_J) is free of rank m^d - Q_k(m)); control: dropping one matching gives p-torsion at some p | m.
import sys, itertools, numpy as np
exec(open('chk28.py').read().split('good = ')[0])
def rows_of(m, k, p, drop=None):
    d = 2*k + 1; cols = list(itertools.product(range(m), repeat=d)); idx = {e: i for i, e in enumerate(cols)}
    R = []
    Js = list(matchings_list(list(range(2*k + 2))))
    if drop is not None: Js = [J for i, J in enumerate(Js) if i != drop]
    for J in Js:
        P = psi(J, m, d, p)
        for nu in cols:
            v = np.zeros(len(cols), dtype=np.int64)
            for e, c in P.items(): v[idx[tuple((x + y) % m for x, y in zip(e, nu))]] = c
            R.append(v)
    return np.array(R)
def rank_fast(A, p):
    A = A % p; r = 0
    for c in range(A.shape[1]):
        nz = np.nonzero(A[:, c])[0]
        if len(nz) == 0: continue
        piv = nz[0]; row = A[piv] * pow(int(A[piv, c]), p - 2, p) % p
        others = nz[1:]
        if len(others): A[others] = (A[others] - np.outer(A[others, c], row)) % p
        A = np.delete(A, piv, axis=0); r += 1
        if A.shape[0] == 0: break
    return r
primes = [2, 3, 5, 7, 11, 13, 1000003]
cells = [(3,1), (5,1), (7,1), (9,1), (3,2), (15,1)]
fails = 0
for (m, k) in cells:
    Q = Qk(k, m); ranks = {}
    for p in primes:
        if m == 15 and p not in (2, 3, 5, 1000003): continue
        ranks[p] = rank_fast(rows_of(m, k, p), p)
    ok = all(v == Q for v in ranks.values()); fails += (not ok)
    print(f"m={m} k={k} Q={Q} ranks={ranks} free rank={m**(2*k+1)-Q} {'OK' if ok else 'FAIL'}", flush=True)
for (m, k) in [(9,1), (3,2)]:
    ps = sorted({f for f in range(2, m+1) if m % f == 0 and all(f % e for e in range(2, f))})
    for drop in range(len(list(matchings_list(list(range(2*k+2)))))):
        r0 = rank_fast(rows_of(m, k, 1000003, drop), 1000003); rp = {p: rank_fast(rows_of(m, k, p, drop), p) for p in ps}
        print(f"control m={m} k={k} drop matching {drop}: rank over large prime {r0}, over p|m {rp} -> {'torsion' if any(v != r0 for v in rp.values()) else 'no torsion'}", flush=True)
print("failures", fails)
