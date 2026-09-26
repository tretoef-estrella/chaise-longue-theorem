# Section 5, item 1: the strengthening.  Direct test: M = Z[y]/(V_{Lambda,Z} + (y_i^{q-1})) should be a FREE Z-module of rank (q-1)^m - |Z_Lambda|
# (Smith normal form over Z of the integer matrix of monomial multiples of the generators, reduced mod the box).
# Prediction: no torsion, rank = |Z_Lambda|, at the root (D_J) for (k,q)=(1,5),(1,7),(2,3),(1,9) and for every down-set at (q,m)=(5,3),(7,3),(9,3),(5,4).
# Estimate: largest matrix 3*512 x 512 ((1,9)) / gens*256 x 256; < 1 min, < 400 MB.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import *
def zform(gens, m, q):
    monos=list(itertools.product(range(q-1),repeat=m)); col={e:i for i,e in enumerate(monos)}
    rows=[]
    for g in gens:
        for u in monos:
            r=[0]*len(monos); nz=False
            for e,c in g.items():
                ee=tuple(x+y for x,y in zip(e,u))
                if all(x<=q-2 for x in ee): r[col[ee]]+=c; nz=True
            if nz: rows.append(r)
    if not rows: return 0,[]
    ed=matrix(ZZ,rows).elementary_divisors()
    nz=[d for d in ed if d!=0]
    return len(nz), [d for d in nz if abs(d)!=1]
for (k,q) in [(1,5),(1,7),(2,3),(1,9)]:
    m=2*k+1; N=2*k+2
    gens=[]
    for J in matchings(range(N)):
        g=const(1,m)
        for a,b in J:
            if a==0: continue
            g=poly_mul(g,D_poly(a-1,b-1,q,m))
        gens.append(g)
    t0=time.time(); rk,tors=zform(gens,m,q)
    print("root (k,q)=(%d,%d): rank of V_Z = %d (Q_k(q)=%d); torsion of Z[y]/(V_Z+box): %s ; %.1fs"%(k,q,rk,Qk(k,q),tors if tors else "NONE (free)",time.time()-t0), flush=True)
for (q,m) in [(5,3),(7,3),(9,3),(5,4)]:
    h=(q-1)//2; P=Par(m,h); bad=0; n=0
    for Lam in downsets(P):
        rk,tors=zform(V_generators(Lam,m,q),m,q); z=sum(count_shape_formula(l,m,h) for l in Lam); n+=1
        if rk!=z or tors: bad+=1; print("  !!",q,m,sorted(Lam),rk,z,tors)
    print("all down-sets (q,m)=(%d,%d): %d down-sets; rank V_Z = |Z_Lambda| and quotient free in all but %d"%(q,m,n,bad), flush=True)
