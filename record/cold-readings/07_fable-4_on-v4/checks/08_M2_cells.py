"""Generate a Macaulay2 script for the cell (k,q,p): degree of F_p[y]/((D_J)+(y_i^{q-1})), a Groebner engine different from Singular.
Prediction: (q-1)^{2k+1} - degree = Q_k(q)."""
import sys; sys.path.insert(0,'checks')
from lib_chaise import matchings, Qk
k,q,p=[int(x) for x in sys.argv[1].split(',')]
m=2*k+1; N=2*k+2
ys=["y%d"%i for i in range(1,m+1)]
def D(a,b): return "("+"+".join("(%d)*%s^%d*%s^%d"%((-1)**u,ys[a],u,ys[b],q-2-u) for u in range(q-1))+")"
gens=[]
for J in matchings(range(N)):
    f="*".join(D(a-1,b-1) for a,b in J if a!=0)
    gens.append(f)
box=",".join("%s^%d"%(y,q-1) for y in ys)
print('R = ZZ/%d[%s];'%(p,",".join(ys)))
print('I = ideal(%s) + ideal(%s);'%(",".join(gens),box))
print('d = degree (R/I);')
print('<< "(k,q)=(%d,%d) over F_%d [M2]: dim (D_J)C = " << (%d - d) << " ; Q_k(q) = %d ; " << (if %d - d == %d then "EQUAL" else "DIFFERENT") << endl;'%(k,q,p,(q-1)**m,Qk(k,q),(q-1)**m,Qk(k,q)))
print('exit 0;')
