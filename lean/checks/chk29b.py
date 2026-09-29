import sys, itertools, numpy as np
exec(open('chk28.py').read().split('good = ')[0])
def matrix(m, k, p, drop=None, dtype=np.int32):
    d = 2*k + 1; cols = list(itertools.product(range(m), repeat=d)); idx = {e: i for i, e in enumerate(cols)}
    Js = list(matchings_list(list(range(2*k + 2))))
    if drop is not None: Js = [J for i, J in enumerate(Js) if i != drop]
    A = np.zeros((len(Js)*len(cols), len(cols)), dtype=dtype); r = 0
    for J in Js:
        P = list(psi(J, m, d, p).items())
        for nu in cols:
            for e, c in P: A[r, idx[tuple((x + y) % m for x, y in zip(e, nu))]] = c
            r += 1
    return A
def rank_mask(A, p):
    alive = np.ones(A.shape[0], dtype=bool); r = 0
    for c in range(A.shape[1]):
        nz = np.nonzero(alive & (A[:, c] != 0))[0]
        if len(nz) == 0: continue
        piv = nz[0]; row = (A[piv].astype(np.int64) * pow(int(A[piv, c]), p - 2, p) % p).astype(A.dtype)
        o = nz[1:]
        if len(o): A[o] = (A[o] - (A[o, c][:, None] * row) % p) % p
        alive[piv] = False; r += 1
    return r
mode = sys.argv[1]
if mode == 'm15':
    Q = Qk(1, 15)
    for p in (2, 3, 5):
        print(f"m=15 k=1 p={p}: rank={rank_mask(matrix(15, 1, p), p)} Q={Q}", flush=True)
else:
    for (m, k) in [(9,1), (3,2)]:
        ps = sorted({f for f in range(2, m+1) if m % f == 0 and all(f % e for e in range(2, f))})
        nJ = len(list(matchings_list(list(range(2*k+2)))))
        for drop in range(nJ):
            r0 = rank_mask(matrix(m, k, 1000003, drop, np.int64), 1000003)
            rp = {p: rank_mask(matrix(m, k, p, drop), p) for p in ps}
            print(f"control m={m} k={k} drop {drop}: rank over large prime {r0}, over p|m {rp} -> {'p-torsion' if any(v != r0 for v in rp.values()) else 'no torsion'}", flush=True)
