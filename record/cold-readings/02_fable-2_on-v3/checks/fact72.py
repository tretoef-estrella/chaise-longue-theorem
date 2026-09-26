"""Fact 7.2: q=9, k=2, K = J \ {[[0,1],[2,3],[4,5]], [[0,2],[1,5],[3,4]]}.
PREDICTION (paper): dim (D_J: J in K)C = 4730, |Gamma_K| = 4736; full family: 5120 = Q_2(9), |Gamma_J| = 5120."""
import time
from boxalg import *
from sform import run
k, q = 2, 9
allJ = matchings(6)
ex = [((0,1),(2,3),(4,5)), ((0,2),(1,5),(3,4))]
assert all(e in allJ for e in ex)
t=time.time()
print("Gamma full:", gamma_count(k, q, allJ), " Q_2(9) =", Q(2,9), f"({time.time()-t:.1f}s)", flush=True)
K = [J for J in allJ if J not in ex]
print("Gamma_K:", gamma_count(k, q, K), flush=True)
run(k, q, exclude=ex, verbose=False)
run(k, q, verbose=False)
