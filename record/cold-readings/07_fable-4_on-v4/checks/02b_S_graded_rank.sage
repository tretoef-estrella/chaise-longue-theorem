# Cross-check of 02 by a different route: graded rank.  (D_J)C is homogeneous; in each degree d the span of {u*D_J : u monomial}
# reduced modulo the box (drop monomials with an exponent >= q-1) is computed as the rank of an explicit matrix over GF(p).
# Prediction: total = Q_k(q) and (for (1,9),(2,9) over F_3) the graded ranks of the paper's table 8.1.
# Estimate: (2,7): per-degree matrices at most (15*780) x 780 over GF(7) ~ 36 MB; (1,25): 3 vars, exps<=23, per degree <= 3*~430 x 430; < 2 min, < 400 MB.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import Qk, matchings, D_poly, poly_mul, const
def run(k,q,p, show=False):
    m=2*k+1; N=2*k+2; F=GF(p)
    gens=[]
    for J in matchings(range(N)):
        g=const(1,m)
        for (a,b) in J:
            if a==0: continue
            g=poly_mul(g, D_poly(a-1,b-1,q,m))
        gens.append(g)
    deg0=k*(q-2)
    monos={}
    for e in itertools.product(range(q-1),repeat=m):
        monos.setdefault(sum(e),[]).append(e)
    t0=time.time(); total=0; ranks=[]
    for d in sorted(monos):
        if d<deg0: continue
        cols={e:i for i,e in enumerate(monos[d])}
        rows=[]
        for u in monos.get(d-deg0,[]):
            for g in gens:
                r=[0]*len(cols)
                for e,c in g.items():
                    ee=tuple(x+y for x,y in zip(e,u))
                    if all(x<=q-2 for x in ee): r[cols[ee]]=(r[cols[ee]]+c)%p
                rows.append(r)
        if not rows: ranks.append(0); continue
        M=matrix(F,rows); rk=M.rank(); ranks.append(rk); total+=rk
    print("(k,q)=(%d,%d) over F_%d : graded-rank dim = %d ; Q_k(q) = %d ; %s ; %.1fs"%(k,q,p,total,Qk(k,q),"EQUAL" if total==Qk(k,q) else "DIFFERENT", time.time()-t0), flush=True)
    if show: print("   graded ranks from degree %d:"%deg0, ranks, flush=True)
    return total
cells=[(1,3,3,True),(2,3,3,True),(3,3,3,True),(1,9,3,True),(1,5,5,True),(2,5,5,True),(1,7,7,True),(2,7,7,False),(1,25,5,False),(1,7,3,True),(1,7,2,True)]
for c in cells: run(*c)
