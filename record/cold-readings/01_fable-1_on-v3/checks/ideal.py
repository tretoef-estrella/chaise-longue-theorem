# Independent engine: dimension of an ideal in F_p[y_1..y_m]/(y_i^e) (exponents < e), graded, dense numpy elimination mod p.
import numpy as np, itertools
from functools import lru_cache

def monos_of_degree(m,e,d):
    # all exponent tuples in [0,e)^m with sum d
    res=[]
    def rec(i,rem,cur):
        if i==m:
            if rem==0: res.append(tuple(cur))
            return
        for a in range(min(e-1,rem),-1,-1):
            rec(i+1,rem-a,cur+[a])
    rec(0,d,[])
    return res

def rank_mod_p(M,p):
    M=M.copy()%p
    r=0; rows,cols=M.shape
    for c in range(cols):
        if r>=rows: break
        piv=np.nonzero(M[r:,c])[0]
        if len(piv)==0: continue
        i=r+piv[0]
        if i!=r: M[[r,i]]=M[[i,r]]
        inv=pow(int(M[r,c]),p-2,p)
        M[r]=(M[r]*inv)%p
        nz=np.nonzero(M[:,c])[0]
        for i in nz:
            if i!=r:
                M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
    return r

def rowspace_basis_mod_p(M,p):
    M=M.copy()%p
    r=0; rows,cols=M.shape
    for c in range(cols):
        if r>=rows: break
        piv=np.nonzero(M[r:,c])[0]
        if len(piv)==0: continue
        i=r+piv[0]
        if i!=r: M[[r,i]]=M[[i,r]]
        inv=pow(int(M[r,c]),p-2,p)
        M[r]=(M[r]*inv)%p
        nz=np.nonzero(M[:,c])[0]
        for i in nz:
            if i!=r:
                M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
    return M[:r]

def ideal_dim(m,e,p,gens,verbose=False):
    """gens: list of dict {exponent tuple: coeff}. Returns (total dim, graded dims dict)."""
    maxdeg=m*(e-1)
    # bucket generators by degree (assume homogeneous)
    bydeg={}
    for g in gens:
        g={k:v%p for k,v in g.items() if v%p and max(k)<e}
        if not g: continue
        degs={sum(k) for k in g}
        assert len(degs)==1, "non-homogeneous generator"
        bydeg.setdefault(degs.pop(),[]).append(g)
    prev_basis=None; prev_monos=None
    graded={}; total=0
    for d in range(0,maxdeg+1):
        monos=monos_of_degree(m,e,d)
        idx={mo:i for i,mo in enumerate(monos)}
        rows=[]
        # multiply previous basis by each variable
        if prev_basis is not None and len(prev_basis)>0:
            for row in prev_basis:
                nzs=np.nonzero(row)[0]
                for v in range(m):
                    new=np.zeros(len(monos),dtype=np.int64)
                    ok=False
                    for j in nzs:
                        mo=list(prev_monos[j]); mo[v]+=1
                        if mo[v]<e:
                            new[idx[tuple(mo)]]=row[j]; ok=True
                    if ok: rows.append(new)
        for g in bydeg.get(d,[]):
            new=np.zeros(len(monos),dtype=np.int64)
            for k,v in g.items(): new[idx[k]]=v
            rows.append(new)
        if rows:
            M=np.array(rows,dtype=np.int64)
            basis=rowspace_basis_mod_p(M,p)
        else:
            basis=np.zeros((0,len(monos)),dtype=np.int64)
        graded[d]=basis.shape[0]; total+=basis.shape[0]
        if verbose: print(" deg",d,"monos",len(monos),"rank",basis.shape[0],flush=True)
        prev_basis=basis; prev_monos=monos
    return total,graded

# polynomial helpers (dicts)
def padd(a,b,p):
    r=dict(a)
    for k,v in b.items():
        r[k]=(r.get(k,0)+v)%p
    return {k:v for k,v in r.items() if v}
def pmul(a,b,p,e=None):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2))
            if e is not None and max(k)>=e: continue
            r[k]=(r.get(k,0)+v1*v2)%p
    return {k:v for k,v in r.items() if v}
def var(i,m,power=1):
    k=[0]*m; k[i]=power; return {tuple(k):1}
def const(c,m):
    return {tuple([0]*m):c}
