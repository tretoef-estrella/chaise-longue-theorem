# Step 4: (S) over F_p by my own construction of D_J and Singular's vector_space_dimension (route: colength of (D_J)+(y_i^{q-1})).
# Prediction: dim (D_J)C = Q_k(q) in every cell in the right characteristic; also = Q_k(q) when char not | q-1 (Thm 5.9);
# no prediction when char | q-1.  Estimate: largest cell (2,7): C_5 of dim 7776, 15 generators of degree 10, 5 variables:
# Singular std, < 3 min, < 500 MB.  Cells run smallest first; each line is flushed.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import Qk, matchings
def run(k,q,p):
    m=2*k+1; N=2*k+2
    R=PolynomialRing(GF(p), m, 'y'); y=R.gens()
    def D(a,b): return sum((-1)^u * y[a]^u * y[b]^(q-2-u) for u in range(q-1))
    gens=[]
    for J in matchings(range(N)):
        g=R(1)
        for (a,b) in J:
            if a==0: continue
            g*=D(a-1,b-1)
        gens.append(g)
    box=[v^(q-1) for v in y]
    t0=time.time()
    I=R.ideal(gens+box)
    vsd=I.vector_space_dimension()
    dimV=(q-1)^m - vsd
    print("(k,q)=(%d,%d) over F_%d : dim (D_J)C = %d ; Q_k(q) = %d ; %s ; %.1fs"%(k,q,p,dimV,Qk(k,q), "EQUAL" if dimV==Qk(k,q) else ("dim>Q" if dimV>Qk(k,q) else "dim<Q  <-- would contradict Thm 5.3"), time.time()-t0), flush=True)
    return dimV
cells=[(1,3,3),(1,5,5),(1,7,7),(2,3,3),(1,9,3),(1,11,11),(1,13,13),(3,3,3),(2,5,5),(1,25,5),(2,7,7),
       # other characteristics: Theorem 5.9 predicts equality when p does not divide q-1
       (1,5,3),(1,5,7),(2,5,3),(1,7,5),(1,7,11),(1,9,5),(1,9,7),(2,5,11),(1,11,3),(1,13,5),(1,13,7),
       # p | q-1 : measured only
       (1,5,2),(1,7,2),(1,7,3),(2,7,3),(2,7,2),(1,9,2),(1,13,3),(1,13,2),(2,5,2),(1,11,5),(1,11,2)]
if len(sys.argv)>1: cells=[tuple(int(x) for x in c.split(',')) for c in sys.argv[1:]]
for (k,q,p) in cells: run(k,q,p)
