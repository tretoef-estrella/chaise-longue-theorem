# Section 6 experiments. Predictions are printed BEFORE each computation.
import sys, itertools, time
import numpy as np
from ideal import *
from sform import D, matchings
from fact72 import Q

def yform(k,q,p):
    m=2*k+1; e=q-1; gens=[]
    for J in matchings(list(range(2*k+2))):
        g=const(1,m)
        for (a,b) in J:
            if a==0: continue
            g=pmul(g,D(a-1,b-1,m,q,p),p,e)
        gens.append(g)
    return ideal_dim(m,e,p,gens)[0]

# literal [DS] form: F_p[t_1..t_n]/(t_i^m - 1) / (psi_J)
def tform(k,m,p):
    n=2*k+1
    monos=list(itertools.product(range(m),repeat=n)); idx={mo:i for i,mo in enumerate(monos)}
    def tmul(a,b):
        r={}
        for k1,v1 in a.items():
            for k2,v2 in b.items():
                kk=tuple((x+y)%m for x,y in zip(k1,k2)); r[kk]=(r.get(kk,0)+v1*v2)%p
        return {kk:v for kk,v in r.items() if v}
    def tvar(i,pw=1):
        kk=[0]*n; kk[i]=pw%m; return {tuple(kk):1}
    def phi(poly):  # phi(u)=sum_{s<m} u^s
        r={}; u=const(1,n)
        for s in range(m):
            for kk,v in u.items(): r[kk]=(r.get(kk,0)+v)%p
            u=tmul(u,poly)
        return {kk:v for kk,v in r.items() if v}
    gens=[]
    for J in matchings(list(range(2*k+2))):
        g=const(1,n)
        for (a,b) in J:
            if a==0:
                g=tmul(g,padd(tvar(b-1),const(-1,n),p))
            else:
                g=tmul(g,padd(tvar(b-1),const(-1,n),p))
                g=tmul(g,phi(tmul(tvar(a-1),tvar(b-1))))
        gens.append(g)
    # closure under multiplication by t_i, incremental echelon
    N=len(monos)
    basis=np.zeros((0,N),dtype=np.int64); pivots=[]
    def reduce(v):
        v=v%p
        for row,pc in zip(basis,pivots):
            if v[pc]: v=(v-v[pc]*row)%p
        return v
    queue=[]
    for g in gens:
        v=np.zeros(N,dtype=np.int64)
        for kk,c in g.items(): v[idx[kk]]=c
        queue.append(v)
    while queue:
        v=reduce(queue.pop())
        nz=np.nonzero(v)[0]
        if len(nz)==0: continue
        pc=nz[0]; v=(v*pow(int(v[pc]),p-2,p))%p
        # keep basis reduced: eliminate pc from existing rows
        for i in range(len(basis)):
            if basis[i,pc]: basis[i]=(basis[i]-basis[i,pc]*v)%p
        basis=np.vstack([basis,v]); pivots.append(pc)
        # multiply by each t_i
        for i in range(n):
            w=np.zeros(N,dtype=np.int64)
            for j in np.nonzero(v)[0]:
                mo=list(monos[j]); mo[i]=(mo[i]+1)%m; w[idx[tuple(mo)]]=v[j]
            queue.append(w)
    return N-len(basis)

if __name__=="__main__":
    which=sys.argv[1]
    if which=="y":
        for (k,q,p) in [(1,5,5),(2,5,5),(1,7,7),(2,7,7),(1,25,5),(3,5,5)]:
            print(f"PREDICTION: y-form over F_{p} at (k,q)=({k},{q}) = Q_k(q) = {Q(k,q)}",flush=True)
            t=time.time(); d=yform(k,q,p)
            print(f"RESULT: {d}  ({'match' if d==Q(k,q) else 'MISMATCH'}, {time.time()-t:.1f}s)",flush=True)
    if which=="t":
        for (k,m,p) in [(1,5,5),(1,7,7),(2,5,5),(1,4,2),(1,6,2),(1,6,3),(1,10,2),(1,10,5),(1,15,3),(1,15,5),(1,9,3)]:
            # |Gamma| for general m: constant term of (sum over mu_m\{1}) ... use DS polynomial for n=2: 3m^2-9m+6+delta_m
            if k==1: G=3*m*m-9*m+6+(1 if m%2==0 else 0)
            else: G=15*m**3-90*m**2+175*m-100+(15*m-39)*(1 if m%2==0 else 0)
            print(f"PREDICTION: literal t-form over F_{p} at (k,m)=({k},{m}): dim = m^(2k+1) - |Gamma| = {m**(2*k+1)-G}",flush=True)
            t=time.time(); d=tform(k,m,p)
            print(f"RESULT: {d}  ({'match' if d==m**(2*k+1)-G else 'MISMATCH'}, {time.time()-t:.1f}s)",flush=True)
