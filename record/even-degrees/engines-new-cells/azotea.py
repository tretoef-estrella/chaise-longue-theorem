# azotea.py — Grepy Chats, 2 Oct 2026. Rooftop measurements for even degrees (DS Conjecture 1.2).
# Usage: python3 -u azotea.py true k m p        -> dim_{F_p} of the ideal (psi_J) in F_p[G], group-ring route, vs |Gamma|
#        python3 -u azotea.py two  k q          -> m = q = 2^v, p = 2, in the coordinates s = t-1:
#                                                  dim of the true ideal, of the ideal of leading forms, and both Hilbert functions
import sys, itertools, numpy as np
from collections import Counter

def matchings(pts):
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        b = pts[i]; rest = pts[1:i] + pts[i+1:]
        for M in matchings(rest): yield [(a, b)] + M

def gamma(k, m):
    n1 = 2*k+1; Js = list(matchings(list(range(n1+1))))
    cnt = 0
    for a in itertools.product(range(1, m), repeat=n1):
        for J in Js:
            if all((a[j-1] + a[l-1]) % m == 0 for (j, l) in J if j != 0):
                cnt += 1; break
    return cnt, len(Js)

def rank_f2(vectors):
    basis = {}; piv = []
    for v in vectors:
        while v:
            h = v.bit_length() - 1
            b = basis.get(h)
            if b is None: basis[h] = v; piv.append(h); break
            v ^= b
    return piv

def to_int(arr_flat_perm):
    return int.from_bytes(np.packbits(arr_flat_perm).tobytes(), 'big')

def rank_fp(M, p):
    M = M.astype(np.int16) % p; r = 0; rows, cols = M.shape
    for c in range(cols):
        if r >= rows: break
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]
        if i != r: M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p-2, p); M[r] = (M[r] * inv) % p
        f = M[r+1:, c].copy(); idx = np.nonzero(f)[0]
        if len(idx): M[r+1+idx] = (M[r+1+idx] - np.outer(f[idx], M[r])) % p
        r += 1
    return r

def run_true(k, m, p):
    n1 = 2*k+1; G, nJ = gamma(k, m)
    vecs = []
    for J in matchings(list(range(n1+1))):
        A = np.zeros((m,)*n1, dtype=np.int64); A[(0,)*n1] = 1
        ks = [l for (j, l) in J]
        for l in ks: A = (np.roll(A, 1, axis=l-1) - A) % p
        for (j, l) in J:
            if j == 0: continue
            S = np.zeros_like(A)
            for a in range(m): S += np.roll(np.roll(A, a, axis=j-1), a, axis=l-1)
            A = S % p
        for nu in itertools.product(range(m), repeat=len(ks)):
            B = A
            for l, e in zip(ks, nu):
                if e: B = np.roll(B, e, axis=l-1)
            vecs.append(B.reshape(-1).astype(np.uint8))
    if p == 2: r = len(rank_f2([to_int(v) for v in vecs]))
    else: r = rank_fp(np.array(vecs), p)
    print(f"TRUE k={k} m={m} p={p}: matchings={nJ} dim R={m**n1} |Gamma|={G} dim ideal={r} torsion-free at p: {r == G}", flush=True)

def run_two(k, q):
    n1 = 2*k+1; G, nJ = gamma(k, q)
    shape = (q,)*n1
    deg = np.indices(shape).sum(axis=0).reshape(-1)
    order = np.argsort(deg, kind='stable')            # position 0 = lowest degree
    degsorted = deg[order]; nbits = len(order); pad = (-nbits) % 8
    def pack(A):                                       # highest bit of the int = lowest degree
        return int.from_bytes(np.packbits(np.concatenate([A.reshape(-1)[order], np.zeros(pad, np.uint8)])).tobytes(), 'big')
    def degbit(h): return int(degsorted[nbits + pad - 1 - h])
    def sh(A, a, ax):
        if a == 0: return A
        B = np.zeros_like(A); src = [slice(None)]*n1; dst = [slice(None)]*n1
        src[ax] = slice(0, q-a); dst[ax] = slice(a, q); B[tuple(dst)] = A[tuple(src)]; return B
    true_v, lin_v = [], []
    for J in matchings(list(range(n1+1))):
        ks = [l for (j, l) in J]
        T = np.zeros(shape, np.uint8); T[(0,)*n1] = 1
        for l in ks: T = sh(T, 1, l-1)
        L = T.copy()
        for (j, l) in J:
            if j == 0: continue
            for _ in range(q-1):                       # times (s_j + s_l + s_j s_l)
                T = sh(T, 1, j-1) ^ sh(T, 1, l-1) ^ sh(sh(T, 1, j-1), 1, l-1)
            S = np.zeros_like(L)
            for u in range(q): S ^= sh(sh(L, u, j-1), q-1-u, l-1)   # (s_j+s_l)^(q-1), char 2
            L = S
        for nu in itertools.product(range(q), repeat=len(ks)):
            B, C = T, L
            for l, e in zip(ks, nu): B = sh(B, e, l-1); C = sh(C, e, l-1)
            true_v.append(pack(B)); lin_v.append(pack(C))
    pt = rank_f2(true_v); pl = rank_f2(lin_v)
    ht = Counter(degbit(h) for h in pt); hl = Counter(degbit(h) for h in pl)
    D = max(list(ht) + list(hl) + [0])
    print(f"TWO k={k} q={q}: matchings={nJ} dim B={q**n1} |Gamma|={G} dim ideal={len(pt)} dim leading-form ideal={len(pl)}", flush=True)
    print("  HF gr(ideal)        :", [ht.get(d, 0) for d in range(D+1)], flush=True)
    print("  HF leading-form idl :", [hl.get(d, 0) for d in range(D+1)], flush=True)
    print("  difference by degree:", [ht.get(d, 0) - hl.get(d, 0) for d in range(D+1)], flush=True)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'true': run_true(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    else: run_two(int(sys.argv[2]), int(sys.argv[3]))
    print("FIN-OK", flush=True)
