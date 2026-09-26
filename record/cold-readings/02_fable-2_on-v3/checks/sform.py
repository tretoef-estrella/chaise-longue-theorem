"""(S) in the sum form: dim_{F_3} (D_J : J in K) C, graded, for C=F_3[y_1..y_{2k+1}]/(y_i^{q-1})."""
import sys, time
from boxalg import *

def run(k, q, exclude=(), verbose=True):
    n = 2 * k + 1
    e = q - 1
    allJ = matchings(2 * k + 2)
    K = [J for J in allJ if J not in exclude]
    gens = [D_J(J, q, n, e) for J in K]
    t = time.time()
    dims = graded_ideal_dims(gens, n, e, verbose=verbose)
    tot = sum(dims.values())
    print(f"(k,q)=({k},{q}) |K|={len(K)}  dim (D_J)C = {tot}   graded: {[dims[d] for d in sorted(dims)]}  time {time.time()-t:.1f}s", flush=True)
    return tot, dims

if __name__ == "__main__":
    k = int(sys.argv[1]); q = int(sys.argv[2])
    run(k, q)
