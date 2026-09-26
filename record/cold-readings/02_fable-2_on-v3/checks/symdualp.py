"""(S) in the intersection form of Prop. 2.6, split by the characters of a small 3'-group G of variable permutations.
rank Phi_d = sum_chi rank(Phi_d restricted to the chi-isotypic component). Exact; the only randomness is none.
Rows: G-orbit representatives alpha of degree-d monomials; columns: chi-basis of the target (orbit sums).
The rank is computed by a streaming RREF over GF(3) in C (rank3.c)."""
import sys, time, ctypes, itertools
import numpy as np
from scipy.sparse import coo_matrix
from boxalg import matchings, Q
lib = ctypes.CDLL('./librankp.so')
PF = 3
lib.rank_gfp.restype = ctypes.c_int
lib.rank_gfp.argtypes = [ctypes.c_int64, ctypes.c_int32, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]

def rank_csr(M):
    coo = M.tocoo(); coo.sum_duplicates()
    d = (coo.data % PF).astype(np.int64); k = d != 0
    M2 = coo_matrix((d[k], (coo.row[k], coo.col[k])), shape=coo.shape).tocsr()
    if M2.shape[1] == 0 or M2.nnz == 0: return 0
    rowptr = M2.indptr.astype(np.int64); col = M2.indices.astype(np.int32); val = (M2.data % PF).astype(np.uint8)
    return lib.rank_gfp(M2.shape[0], M2.shape[1], rowptr.ctypes.data, col.ctypes.data, val.ctypes.data, PF)

def run(k, q, group, verbose=True):
    n = 2*k+1; e = q-1
    pw = np.array([e**(n-1-i) for i in range(n)], dtype=np.int64)
    allJ = matchings(2*k+2); nJ = len(allJ)
    # reduction data per J: for variable v: target var tv[v], sign flag sf[v]
    tv = np.zeros((nJ, n), dtype=np.int64); sf = np.zeros((nJ, n), dtype=np.int64)
    for jn, J in enumerate(allJ):
        for (a, b) in J:
            if a == 0: tv[jn, b-1] = b-1
            else: tv[jn, b-1] = b-1; tv[jn, a-1] = b-1; sf[jn, a-1] = 1
    Jindex = {J: i for i, J in enumerate(allJ)}
    # group: list of permutations sigma (tuples of length n); characters: all homs to {+-1}
    G = group
    # characters: need generators; brute force all sign assignments consistent with the group table
    chars = []
    for signs in itertools.product([1, -1], repeat=len(G)):
        chi = dict(zip(G, signs))
        ok = all(chi[tuple(s2[s1[i]] for i in range(n))] == chi[s1]*chi[s2] for s1 in G for s2 in G)
        if ok: chars.append(chi)
    assert len(chars) == len(G), (len(chars), len(G))
    # action of sigma on matchings: sigma'(0)=0, sigma'(i)=sigma(i-1)+1
    def sigmaJ(sig, J):
        sp = lambda i: 0 if i == 0 else sig[i-1]+1
        return tuple(sorted(tuple(sorted((sp(a), sp(b)))) for (a, b) in J))
    # all monomials, grouped by degree
    tot_mon = e**n
    codes = np.arange(tot_mon, dtype=np.int64)
    expo = np.stack([(codes // pw[i]) % e for i in range(n)], axis=1).astype(np.int16)
    deg = expo.sum(axis=1)
    order = np.argsort(deg, kind='stable'); expo = expo[order]; deg = deg[order]
    bounds = np.searchsorted(deg, np.arange(n*(e-1)+2))
    total = 0; prof = {}
    for d in range(n*(e-1)+1):
        t0 = time.time()
        A = expo[bounds[d]:bounds[d+1]].astype(np.int64)   # rows: all monomials of degree d
        if len(A) == 0: continue
        # row orbit representatives
        codeA = A @ pw
        minc = codeA.copy()
        for sig in G:
            inv = np.empty(n, dtype=np.int64); 
            for i in range(n): inv[sig[i]] = i
            # (sigma alpha)[sigma(i)] = alpha[i]  =>  (sigma alpha)[j] = alpha[inv[j]]
            minc = np.minimum(minc, A[:, inv] @ pw)
        A = A[codeA == minc]
        # target basis of degree d: (J, m) with m in J's free vars; build ids = jn*e^n + code(m_full)
        ids = []; 
        for jn, J in enumerate(allJ):
            free = sorted(set(tv[jn]))
            # monomials of degree d in the free vars, exps <= e-1
            for comb in itertools.product(range(e), repeat=k):  # first k exps, last determined
                s = sum(comb); last = d - s
                if 0 <= last <= e-1:
                    mfull = np.zeros(n, dtype=np.int64); 
                    for idx, v in enumerate(free[:-1]): mfull[v] = comb[idx]
                    mfull[free[-1]] = last
                    ids.append(jn*tot_mon + int(mfull @ pw))
        ids = np.array(sorted(ids), dtype=np.int64); nT = len(ids)
        if nT == 0: continue
        Tj = ids // tot_mon; Tm = ids % tot_mon
        Texp = np.stack([(Tm // pw[i]) % e for i in range(n)], axis=1)
        # action of each sigma on the target basis: img[s][i] index, sg[s][i] sign (+1/-1)
        img = []; sgn = []
        for sig in G:
            inv = np.empty(n, dtype=np.int64)
            for i in range(n): inv[sig[i]] = i
            newJ = np.array([Jindex[sigmaJ(sig, J)] for J in allJ], dtype=np.int64)[Tj]
            pm = Texp[:, inv]                     # permuted exponent vector: pm[j] = m[inv[j]]
            # reduce under newJ: exponent goes to tv[newJ, v], sign (-1)^{exp} if sf[newJ, v]
            red = np.zeros_like(pm); sflag = np.zeros(nT, dtype=np.int64)
            for v in range(n):
                np.add.at(red, (np.arange(nT), tv[newJ, v]), pm[:, v])
                sflag += sf[newJ, v] * pm[:, v]
            nid = newJ*tot_mon + red @ pw
            pos = np.searchsorted(ids, nid); assert np.all(ids[pos] == nid)
            img.append(pos); sgn.append(np.where(sflag % 2 == 0, 1, -1))
        img = np.array(img); sgn = np.array(sgn)
        rep = img.min(axis=0)                                # orbit representative index for each target element
        is_rep = rep == np.arange(nT)
        # for each element i: a sigma and sign with sigma.[rep_i] = s [t_i]
        sigma_of = np.zeros(nT, dtype=np.int64); s_of = np.zeros(nT, dtype=np.int64)
        reps = np.nonzero(is_rep)[0]
        for si in range(len(G)):
            sigma_of[img[si][reps]] = si; s_of[img[si][reps]] = sgn[si][reps]
        # rows: for each rep alpha and each J: (target index, sign)
        nA = len(A); rowJ = np.zeros((nJ, nA), dtype=np.int64); rowS = np.zeros((nJ, nA), dtype=np.int64); rowOK = np.zeros((nJ, nA), dtype=bool)
        for jn in range(nJ):
            red = np.zeros_like(A); sflag = np.zeros(nA, dtype=np.int64)
            for v in range(n):
                np.add.at(red, (np.arange(nA), np.full(nA, tv[jn, v])), A[:, v])
                sflag += sf[jn, v] * A[:, v]
            ok = (red.max(axis=1) <= e-1)
            nid = jn*tot_mon + red @ pw
            pos = np.searchsorted(ids, np.where(ok, nid, ids[0]))
            pos = np.minimum(pos, nT-1)
            ok &= (ids[pos] == nid)
            rowJ[jn] = pos; rowS[jn] = np.where(sflag % 2 == 0, 1, -1); rowOK[jn] = ok
        rk_d = 0
        for chi in chars:
            chv = np.array([chi[s] for s in G], dtype=np.int64)
            kappa = np.zeros(nT, dtype=np.int64)
            for si in range(len(G)):
                fixed = img[si] == np.arange(nT)
                kappa += np.where(fixed, chv[si]*sgn[si], 0)
            colrep = np.full(nT, -1, dtype=np.int64)
            good = is_rep & (kappa % PF != 0)
            colrep[good] = np.arange(good.sum())
            ncols = int(good.sum())
            if ncols == 0: continue
            coef = s_of * chv[sigma_of]                       # c_chi(t) = s * chi(sigma)
            col_of = colrep[rep]                             # column of the orbit of t (or -1)
            rows_i = []; cols_i = []; vals_i = []
            for jn in range(nJ):
                ok = rowOK[jn] & (col_of[rowJ[jn]] >= 0)
                rows_i.append(np.nonzero(ok)[0]); cols_i.append(col_of[rowJ[jn]][ok]); vals_i.append((rowS[jn][ok]*coef[rowJ[jn]][ok]) % PF)
            M = coo_matrix((np.concatenate(vals_i).astype(np.int64), (np.concatenate(rows_i), np.concatenate(cols_i))), shape=(nA, ncols))
            rk_d += rank_csr(M)
        prof[d] = rk_d; total += rk_d
        if verbose: print(f"  deg {d}: monomials {bounds[d+1]-bounds[d]} row-reps {nA} target {nT} rank {rk_d} ({time.time()-t0:.1f}s)", flush=True)
    print(f"FIELD F_{PF}: (k,q)=({k},{q}) sym-intersection form: b_k(q-1) = {total}   Q_k(q) = {Q(k,q)}   graded {[prof[d] for d in sorted(prof) if prof[d]]}", flush=True)
    return total, prof

if __name__ == "__main__":
    k = int(sys.argv[1]); q = int(sys.argv[2]); n = 2*k+1
    PF = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 3
    if n == 3: G = [(0,1,2), (1,0,2)]
    else:
        G = [tuple(range(n)), (1,0,3,2)+tuple(range(4,n)), (2,3,0,1)+tuple(range(4,n)), (3,2,1,0)+tuple(range(4,n))]
    run(k, q, G, verbose=('-v' in sys.argv))
