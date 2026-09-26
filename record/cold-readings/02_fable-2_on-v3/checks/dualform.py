"""(S) in the intersection form of Prop. 2.6:
 b_k(q-1) = rank of Phi: F_3[y]/(y_i^{q-1}) -> (+)_J F_3[y]/(I'_J + (y_i^{q-1})),  graded by degree.
For J with pairs (j_i,k_i), j_i<k_i, j_0=0: modulo I'_J, y_{j_i} = -y_{k_i}; basis of the J-component:
monomials in y_{k_0}, y_{k_1},..,y_{k_k} with exponents <= q-2.
Independent of the sum form: no D_J is ever formed."""
import sys, time
from boxalg import matchings, monomials_of_degree, Q, P
import flint

def run(k, q, verbose=True, degrees=None):
    n = 2*k+1; e = q-1
    allJ = matchings(2*k+2)
    # for each J: map variable index (0..n-1, i.e. y_1..y_n) -> (target var index, sign)
    Jdata = []
    for J in allJ:
        tgt = {}   # var -> (free var, sign exponent)
        free = []
        for (a,b) in J:
            if a == 0:
                free.append(b-1); tgt[b-1] = (b-1, 0)
            else:
                free.append(b-1); tgt[b-1] = (b-1, 0); tgt[a-1] = (b-1, 1)
        Jdata.append((sorted(free), tgt))
    total = 0; prof = {}
    degs = range(0, n*(e-1)+1) if degrees is None else degrees
    for d in degs:
        rowsm = monomials_of_degree(n, e, d)
        # target columns: for each J, monomials of degree d in its k+1 free vars, exps<=e-1
        colidx = {}
        for jn,(free,tgt) in enumerate(Jdata):
            for m in monomials_of_degree(k+1, e, d):
                colidx[(jn, m)] = len(colidx)
        if not rowsm or not colidx:
            prof[d] = 0; continue
        M = flint.nmod_mat(len(rowsm), len(colidx), P)
        for i, al in enumerate(rowsm):
            for jn,(free,tgt) in enumerate(Jdata):
                ex = [0]*(k+1); sgn = 0
                pos = {v:i2 for i2,v in enumerate(free)}
                ok = True
                for v in range(n):
                    if al[v]==0: continue
                    fv, s = tgt[v]
                    ex[pos[fv]] += al[v]
                    if s: sgn += al[v]
                if max(ex) >= e: continue
                M[i, colidx[(jn, tuple(ex))]] = (P-1) if (sgn % 2) else 1
        t=time.time(); rk = M.rank(); prof[d]=rk; total += rk
        if verbose: print(f"  deg {d}: rows {len(rowsm)} cols {len(colidx)} rank {rk} ({time.time()-t:.1f}s)", flush=True)
    print(f"(k,q)=({k},{q}) intersection form: b_k(q-1) = {total}   Q_k(q) = {Q(k,q)}   graded {[prof[d] for d in sorted(prof) if prof[d]]}", flush=True)
    return total, prof

if __name__ == "__main__":
    k=int(sys.argv[1]); q=int(sys.argv[2])
    run(k,q, verbose=('-v' in sys.argv))
