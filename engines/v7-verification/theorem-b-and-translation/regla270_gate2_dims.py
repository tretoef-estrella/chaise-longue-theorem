# Gate 2 (algebraic): for down-sets Lambda of Par_m, dim_F3 V_Lambda (ideal of tight patterns in F3[y]/(y^{q-1}))
# versus |Z_Lambda| (counted by the class DP of gate1). Own pattern generator, own rank engine.
import sys, itertools, numpy as np, time
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from regla270_gate1_downsets import Par, Ncount, downsets, canon  # repo copy: 'gate1' was a local copy of regla270_gate1_downsets.py
p=3
q=int(sys.argv[1]); m=int(sys.argv[2]); lim=int(sys.argv[3]) if len(sys.argv)>3 else 10**6
h=(q-1)//2; n=q-1
def pmul(P,Q):
    R={}
    for e,c in P.items():
        for f,d in Q.items():
            g=tuple(x+y for x,y in zip(e,f))
            if max(g)>=n: continue
            R[g]=(R.get(g,0)+c*d)%p
    return {e:c for e,c in R.items() if c}
def var(i,ex=1): e=[0]*m; e[i]=ex; return {tuple(e):1}
def lin(i,j,s): # y_i + s*y_j
    P=dict(var(i)); P.update({k:(v*s)%p for k,v in var(j).items()}); return P
def D(a,b):
    P={}
    for u in range(q-1):
        e=[0]*m; e[a]+=u; e[b]+=q-2-u; P[tuple(e)]=((-1)**u)%p
    return P
def Vand(B):
    P={tuple([0]*m):1}
    for a,b in itertools.combinations(sorted(B),2): P=pmul(P,lin(a,b,-1))
    return P
def conj(l): return [sum(1 for x in l if x>c) for c in range(l[0])] if l else []
def set_partitions_sizes(items,sizes):
    if not sizes: 
        if not items: yield []
        return
    s=sizes[0]
    for B in itertools.combinations(items,s):
        rest=[x for x in items if x not in B]
        for r in set_partitions_sizes(rest,sizes[1:]): yield [B]+r
def matchings_of(items,k):
    # all sets of k disjoint pairs inside items
    for sub in itertools.combinations(items,2*k):
        def rec(s):
            if not s: yield []; return
            a=s[0]
            for i in range(1,len(s)):
                for r in rec(s[1:i]+s[i+1:]): yield [(a,s[i])]+r
        yield from ((pairs,[x for x in items if x not in sub]) for pairs in rec(list(sub)))
def tight_patterns(lam):
    s=(m-sum(lam))//2; cols=conj(lam); out=[]
    for pairs,rest in matchings_of(list(range(m)),s):
        for blocks in set_partitions_sizes(rest,cols):
            P={tuple([0]*m):1}
            for a,b in pairs: P=pmul(P,D(a,b))
            for B in blocks: P=pmul(P,Vand(B))
            if P: out.append(P)
    return out
mons=sorted(itertools.product(range(n),repeat=m),key=sum)
bydeg={}
for e in mons: bydeg.setdefault(sum(e),[]).append(e)
idx={d:{e:i for i,e in enumerate(L)} for d,L in bydeg.items()}
def echelon(A):
    A=A%3; r=0; rows,cols=A.shape
    for c in range(cols):
        if r==rows: break
        nz=np.nonzero(A[r:,c])[0]
        if len(nz)==0: continue
        i=r+nz[0]
        if i!=r: A[[r,i]]=A[[i,r]]
        if A[r,c]==2: A[r]=(A[r]*2)%3
        f=A[r+1:,c].copy()
        if f.any(): A[r+1:]=(A[r+1:]-np.outer(f,A[r]))%3
        r+=1
    return A[:r]
def ideal_dim(gens):
    gd={}
    for P in gens:
        d=sum(next(iter(P))); gd.setdefault(d,[]).append(P)
    prev=None; tot=0; maxd=m*(n-1)
    for d in range(0,maxd+1):
        cols=len(bydeg[d]); rows=[]
        for P in gd.get(d,[]):
            v=np.zeros(cols,dtype=np.int64)
            for e,c in P.items(): v[idx[d][e]]=c
            rows.append(v)
        if prev is not None and len(prev):
            pd=bydeg[d-1]
            for b in prev:
                for i in range(m):
                    v=np.zeros(cols,dtype=np.int64)
                    for k in np.nonzero(b)[0]:
                        e=list(pd[k]); e[i]+=1
                        if e[i]<n: v[idx[d][tuple(e)]]=b[k]
                    rows.append(v)
        prev=echelon(np.array(rows)) if rows else np.zeros((0,cols),dtype=np.int64)
        tot+=len(prev)
    return tot
Nm=Ncount(m,h); Pm=Par(m,h); DS=downsets(Pm,lim)
pat={l:tight_patterns(l) for l in Pm}
bad=0; t0=time.time()
for Lam in DS:
    gens=[P for l in Lam for P in pat[l]]
    dv=ideal_dim(gens) if gens else 0
    z=sum(Nm.get(l,0) for l in Lam)
    ok = dv>=z; bad+= (not ok)
    print(sorted(Lam), "dimV=",dv,"|Z|=",z, "OK" if ok else "FAIL", "EQ" if dv==z else "")
print(f"q={q} m={m} downsets={len(DS)} fails(dim<|Z|)={bad} t={time.time()-t0:.1f}s")
