# Step 9b: Theorem B for composite odd q (not a prime power): the claim is purely algebraic.  Prediction: dim (D_J)C_F = Q_1(q) when char F does not divide q-1
# (q=15 over F_3, F_5; q=21 over F_3, F_11); no claim when char | q-1 (q=15 over F_7, q=21 over F_5); >= always.  Also every down-set at (q,m)=(15,3),(21,3).
# Estimate: C_3 of dim 14^3=2744 / 20^3=8000; < 2 min, < 400 MB.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import *
for (q,p) in [(15,3),(15,5),(15,7),(15,2),(21,3),(21,11),(21,5),(21,2),(45,7)]:
    k=1; m=3
    R=PolynomialRing(GF(p),m,'y'); y=R.gens()
    D=lambda a,b: sum((-1)^u*y[a]^u*y[b]^(q-2-u) for u in range(q-1))
    gens=[]
    for J in matchings(range(4)):
        g=R(1)
        for a,b in J:
            if a==0: continue
            g*=D(a-1,b-1)
        gens.append(g)
    t0=time.time(); I=R.ideal(gens+[v^(q-1) for v in y]); d=(q-1)^m-I.vector_space_dimension()
    print("composite q=%d over F_%d [%s]: dim (D_J)C = %d ; Q_1(q) = %d ; %s ; %.1fs"%(q,p,"Thm 5.9 applies" if (q-1)%p else "p | q-1 (no claim)",d,Qk(1,q),"EQUAL" if d==Qk(1,q) else ("dim<Q !!" if d<Qk(1,q) else "dim>Q"),time.time()-t0), flush=True)
for (q,m,p) in [(15,3,3),(15,3,7),(15,4,5),(21,3,11)]:
    h=(q-1)//2; P=Par(m,h); bad=0; strict=0; n=0
    for Lam in downsets(P):
        R=PolynomialRing(GF(p),m,'y'); y=R.gens()
        I=R.ideal([R(g) for g in V_generators(Lam,m,q)]+[v^(q-1) for v in y])
        dv=(q-1)^m-I.vector_space_dimension(); z=sum(count_shape_formula(l,m,h) for l in Lam); n+=1
        bad+= dv<z; strict+= dv>z
    print("all down-sets (q,m)=(%d,%d) over F_%d: %d down-sets, dim<|Z|: %d, dim>|Z|: %d"%(q,m,p,n,bad,strict), flush=True)
