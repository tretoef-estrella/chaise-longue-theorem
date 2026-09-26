import itertools, numpy as np
from math import comb
def polymul(f,g,box,p):
    h={}
    for e1,c1 in f.items():
        for e2,c2 in g.items():
            e=tuple(a+b for a,b in zip(e1,e2))
            if any(x>=box for x in e): continue
            h[e]=(h.get(e,0)+c1*c2)%p
    return {e:c for e,c in h.items() if c}
def lin(nv,i,j,p):  # x_i - z_j  as variables index i and j
    e1=[0]*nv; e1[i]=1; e2=[0]*nv; e2[j]=1
    return {tuple(e1):1, tuple(e2):p-1}
def powp(f,k,box,p,nv):
    r={tuple([0]*nv):1}
    for _ in range(k): r=polymul(r,f,box,p)
    return r
def rank_mod(M,p):
    M=M.copy()%p; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=np.nonzero(M[r:,c])[0]
        if len(piv)==0: continue
        pr=r+piv[0]; M[[r,pr]]=M[[pr,r]]
        inv=pow(int(M[r,c]),p-2,p); M[r]=(M[r]*inv)%p
        nz=np.nonzero(M[:,c])[0]
        for i in nz:
            if i!=r: M[i]=(M[i]-M[i,c]*M[r])%p
        r+=1
        if r==rows: break
    return r
def idealdim(gens,nv,box,p):
    # gens homogeneous; compute per degree
    maxdeg=nv*(box-1); total=0
    mons_by_deg={}
    for e in itertools.product(range(box),repeat=nv):
        mons_by_deg.setdefault(sum(e),[]).append(e)
    degs=set(sum(next(iter(g))) for g in gens)
    for D in range(maxdeg+1):
        cols=mons_by_deg.get(D,[]); 
        if not cols: continue
        idx={e:i for i,e in enumerate(cols)}
        rows=[]
        for g in gens:
            dg=sum(next(iter(g)))
            if dg>D: continue
            for mon in mons_by_deg.get(D-dg,[]):
                v=np.zeros(len(cols),dtype=np.int64)
                for e,c in g.items():
                    ee=tuple(a+b for a,b in zip(e,mon))
                    if all(x<box for x in ee): v[idx[ee]]=(v[idx[ee]]+c)%p
                if v.any(): rows.append(v)
        if rows: total+=rank_mod(np.array(rows),p)
    return total
def Ibal(a,q,p):
    nv=2*a; gens=[]
    for s in itertools.permutations(range(a)):
        g={tuple([0]*nv):1}
        for i in range(a): g=polymul(g,powp(lin(nv,i,a+s[i],p),q-1,q,p,nv),q,p)
        if g: gens.append(g)
    return idealdim(gens,nv,q,p)
def Iph(a,q,p):
    nv=2*a+1; gens=[]
    for i0 in range(a+1):
        rest=[i for i in range(a+1) if i!=i0]
        for s in itertools.permutations(range(a)):
            g={tuple([0]*nv):1}
            for ii,i in enumerate(rest): g=polymul(g,powp(lin(nv,i,a+1+s[ii],p),q-1,q,p,nv),q,p)
            if g: gens.append(g)
    return idealdim(gens,nv,q,p)
import sys
P0=1000003
for (a,q,p) in [(1,3,3),(2,3,3),(3,3,3),(1,3,P0),(2,3,P0),(2,5,5),(2,5,P0),(2,7,7)]:
    print("bal",a,q,p,Ibal(a,q,p),flush=True)
for (a,q,p) in [(1,3,3),(2,3,3),(1,3,P0),(2,3,P0),(1,5,5),(1,9,3)]:
    print("ph",a,q,p,Iph(a,q,p),flush=True)
