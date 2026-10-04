# R5 (Grepy Tinta): Lemma 8.12, Corollary 8.13, Corollary 10.8, Theorem 8.15. Own code.
import sys, itertools, time
import numpy as np
from collections import defaultdict, Counter
from fractions import Fraction as Fr
from math import factorial
def rref(M,p):
    M=M.astype(np.int64)%p; nr,nc=M.shape; rr=0; piv=[]
    for c in range(nc):
        if rr==nr: break
        nz=np.flatnonzero(M[rr:,c])
        if nz.size==0: continue
        i=rr+int(nz[0])
        if i!=rr: M[[rr,i]]=M[[i,rr]]
        M[rr]=(M[rr]*pow(int(M[rr,c]),-1,p))%p
        colv=M[:,c].copy(); colv[rr]=0
        nzr=np.flatnonzero(colv)
        if nzr.size: M[nzr]=(M[nzr]-np.outer(colv[nzr],M[rr]))%p
        piv.append(c); rr+=1
    return M[:rr],piv
def rk(rows,p,nc):
    if len(rows)==0: return 0
    return rref(np.array(rows,dtype=np.int64).reshape(-1,nc),p)[0].shape[0]
def nullspace(B,p,nc):
    # vectors v with B v = 0 (B: rows), returns rows spanning the orthogonal complement
    if B.shape[0]==0: return np.eye(nc,dtype=np.int64)
    Rr,piv=rref(B,p); free=[c for c in range(nc) if c not in piv]; out=[]
    for f in free:
        v=np.zeros(nc,dtype=np.int64); v[f]=1
        for i,pc in enumerate(piv): v[pc]=(-Rr[i,f])%p
        out.append(v)
    return np.array(out,dtype=np.int64).reshape(-1,nc)
class Ring:
    def __init__(self,nv,r):
        self.nv=nv; self.r=r; self.monos=defaultdict(list)
        for e in itertools.product(range(r),repeat=nv): self.monos[sum(e)].append(e)
        self.pos={d:{e:i for i,e in enumerate(L)} for d,L in self.monos.items()}
        self.maxdeg=nv*(r-1); self.shift={}
        for d in range(self.maxdeg):
            for j in range(nv):
                src=[];dst=[]
                for i,e in enumerate(self.monos[d]):
                    if e[j]<r-1:
                        f=list(e); f[j]+=1; src.append(i); dst.append(self.pos[d+1][tuple(f)])
                self.shift[(d,j)]=(np.array(src,dtype=int),np.array(dst,dtype=int))
    def ideal(self,polys,p):
        gens=defaultdict(list)
        for P in polys:
            P={k:v%p for k,v in P.items() if v%p}
            if not P: continue
            degs={sum(e) for e in P}; assert len(degs)==1,'non-homogeneous'
            d=degs.pop(); v=np.zeros(len(self.monos[d]),dtype=np.int64)
            for e,c in P.items(): v[self.pos[d][e]]=c
            gens[d].append(v)
        prev=None; basis={}
        for d in range(self.maxdeg+1):
            rows=list(gens.get(d,[]))
            if prev is not None and len(prev):
                for j in range(self.nv):
                    s_,d_=self.shift[(d-1,j)]
                    W=np.zeros((prev.shape[0],len(self.monos[d])),dtype=np.int64); W[:,d_]=prev[:,s_]; rows.extend(list(W))
            B=rref(np.array(rows,dtype=np.int64),p)[0] if rows else np.zeros((0,len(self.monos[d])),dtype=np.int64)
            basis[d]=B; prev=B
        return basis
def dim(b): return sum(B.shape[0] for B in b.values())
def pmul(a,b,r):
    d={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2))
            if max(k)>=r: continue
            d[k]=d.get(k,0)+v1*v2
    return {k:v for k,v in d.items() if v}
def Dp(nv,a,b,r,signs=True):
    d={}
    for u in range(r):
        k=[0]*nv; k[a]+=u; k[b]+=r-1-u; d[tuple(k)]=((-1)**u if signs else 1)
    return d
def pm(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for i in range(1,len(S)):
        for M in pm(S[1:i]+S[i+1:]): yield [(a,S[i])]+M
def prodD(nv,pairs,r,signs=True):
    P={tuple([0]*nv):1}
    for (a,b) in pairs: P=pmul(P,Dp(nv,a,b,r,signs),r)
    return P
def Nr(r,n):
    N=n; I0=[Fr(1,factorial(i//2)**2) if i%2==0 else Fr(0) for i in range(N+1)]
    def mul(a,b):
        c=[Fr(0)]*(N+1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                if i+j<=N: c[i+j]+=x*y
        return c
    s=[Fr(1,factorial(i)) for i in range(N+1)]
    for _ in range((r-1)//2): s=mul(s,I0)
    return int(s[N]*factorial(N))
def esym(nv,j):
    d={}
    for S in itertools.combinations(range(nv),j):
        k=[0]*nv
        for i in S: k[i]=1
        d[tuple(k)]=1
    return d
t0=time.time()
print('== P5.1 / P5.2: the two forms, theta ==')
for (r,N,primes) in [(3,4,[2,3,5]),(3,6,[2,3,5]),(5,4,[2,3,5]),(7,4,[2,7])]:
    RN=Ring(N,r); R1=Ring(N-1,r)
    DP=[prodD(N,M,r) for M in pm(range(N))]
    # (D_J): matchings of {0..N-1}, product over pairs avoiding index 0, in the variables 1..N-1 (ring R1 uses positions 0..N-2)
    DJ=[prodD(N-1,[(a-1,b-1) for (a,b) in M if a!=0],r) for M in pm(range(N))]
    for p in primes:
        bM=RN.ideal(DP,p); bJ=R1.ideal(DJ,p)
        # theta: coefficient of x_0^(r-1) of each basis vector of M (x_0 = variable 0)
        img=defaultdict(list); kernel_dim=0
        for d,B in bM.items():
            for row in B:
                e=d-(r-1)
                v=None
                for i in np.flatnonzero(row):
                    mon=RN.monos[d][i]
                    if mon[0]==r-1:
                        if v is None: v=np.zeros(len(R1.monos[e]),dtype=np.int64)
                        v[R1.pos[e][mon[1:]]]=row[i]
                if v is not None: img[e].append(v)
        dimimg=sum(rk(img[e],p,len(R1.monos[e])) for e in img)
        same=all(rk(list(bJ[e])+img.get(e,[]),p,len(R1.monos[e]))==bJ[e].shape[0]==rk(img.get(e,[]),p,len(R1.monos[e])) for e in bJ)
        print('(r,N)=(%d,%d) p=%d: dim M=%d  dim (D_J)=%d  N_r(N)=%d | dim theta(M)=%d (injective: %s)  theta(M)==(D_J): %s'%(r,N,p,dim(bM),dim(bJ),Nr(r,N),dimimg,dimimg==dim(bM),same)); sys.stdout.flush()
print('== P5.3 / P5.4: Corollary 10.8 ==')
for (r,N) in [(3,4),(3,6),(5,4)]:
    RN=Ring(N,r); Ms=list(pm(range(N))); DP=[prodD(N,M,r) for M in Ms]
    odd=[esym(N,j) for j in range(1,N+1,2)]
    killed=all(not {k:v for k,v in pmul(e,P,r).items()} for e in odd for P in DP)   # exact, over Z
    for p in [3,5,7,2]:
        bM=RN.ideal(DP,p); bE=RN.ideal(odd,p)
        IJ=[RN.ideal([{tuple(1 if i==a else 0 for i in range(N)):1, tuple(1 if i==b else 0 for i in range(N)):1} for (a,b) in M],p) for M in Ms]
        eq_all=True; contained=True; dimint=0
        for d in range(RN.maxdeg+1):
            nc=len(RN.monos[d])
            comp=[nullspace(b[d],p,nc) for b in IJ]              # orthogonal complements of the I_J in degree d
            S=np.vstack(comp) if comp else np.zeros((0,nc),dtype=np.int64)
            Sb=rref(S,p)[0] if S.shape[0] else S
            inter=nullspace(Sb,p,nc)                                # intersection of the I_J in degree d
            dimint+=inter.shape[0]
            rE=bE[d].shape[0]
            if rk(list(inter)+list(bE[d]),p,nc)!=inter.shape[0]: contained=False     # E subset of intersection ?
            if not (rE==inter.shape[0]): eq_all=False
        rN=r**N
        print('(r,N)=(%d,%d) p=%d: e_odd*D_P=0 exactly: %s | dim sum D_P C=%d ; r^N-dim(e_odd)=%d ; colength of intersection=%d ; colength of (e_odd)=%d ; (e_odd) in intersection: %s ; equal: %s'%(r,N,p,killed,dim(bM),rN-dim(bE),rN-dimint,rN-dim(bE),contained,eq_all and contained)); sys.stdout.flush()
print('== P5.5 Theorem 8.15 ==')
r=3
def I_gens(m,J):
    idx=list(range(m)); out=[]
    def subsets_pairs(npairs):
        for U in itertools.combinations(idx,2*npairs):
            for M in pm(U): yield U,M
    if (m-J)%2==0:
        for U,M in subsets_pairs((m-J)//2): out.append(prodD(m,M,r))
    elif J>=1:
        for U,M in subsets_pairs((m-1-J)//2):
            DPp=prodD(m,M,r); rest=[x for x in idx if x not in U]
            for a,b in itertools.combinations(rest,2):
                lin={tuple(1 if i==b else 0 for i in range(m)):1, tuple(1 if i==a else 0 for i in range(m)):-1}
                out.append(pmul(DPp,lin,r))
        for U,M in subsets_pairs((m+1-J)//2): out.append(prodD(m,M,r))
    else:   # J=0, m odd
        for c in idx:
            rest=[x for x in idx if x!=c]
            for M in pm(rest):
                out.append(pmul(prodD(m,M,r),{tuple(2 if i==c else 0 for i in range(m)):1},r))
        for (a,b,c) in itertools.combinations(idx,3):
            rest=[x for x in idx if x not in (a,b,c)]
            V={tuple([0]*m):1}
            for (u,v) in [(a,b),(a,c),(b,c)]:
                V=pmul(V,{tuple(1 if i==v else 0 for i in range(m)):1, tuple(1 if i==u else 0 for i in range(m)):-1},r)
            for M in pm(rest): out.append(pmul(prodD(m,M,r),V,r))
    return out
bad=0; tot=0; strict=0
for m in range(1,7):
    Rm=Ring(m,3)
    zc=Counter(abs(sum(M)) for M in itertools.product((-1,0,1),repeat=m))
    for J in range(0,m+1):
        Z=sum(zc[j] for j in range(0,J+1)); g=I_gens(m,J)
        for p in (2,3,101):
            d=dim(Rm.ideal(g,p)); tot+=1
            if d<Z: bad+=1; print('  !! I(%d,%d) p=%d dim %d < |Z| %d'%(m,J,p,d,Z))
            elif d>Z: strict+=1; print('  I(%d,%d) p=%d dim %d > |Z| %d'%(m,J,p,d,Z))
print('Theorem 8.15: %d ideals*primes tested, dim<|Z|: %d, dim>|Z|: %d, equal: %d'%(tot,bad,strict,tot-bad-strict))
print('== P5.6 control: signs of D removed ==')
for (N,) in [(4,),(6,)]:
    R1=Ring(N-1,3)
    for p in (3,2):
        DJs=[prodD(N-1,[(a-1,b-1) for (a,b) in M if a!=0],3,signs=False) for M in pm(range(N))]
        DJt=[prodD(N-1,[(a-1,b-1) for (a,b) in M if a!=0],3,signs=True) for M in pm(range(N))]
        print('r=3 N=%d p=%d: with signs %d ; signs removed %d ; N_3(N)=%d'%(N,p,dim(R1.ideal(DJt,p)),dim(R1.ideal(DJs,p)),Nr(3,N)))
print('== P5.7 control: even box r=4, k=1 ==')
R1=Ring(3,4)
for p in (2,3,5,10007):
    DJ=[prodD(3,[(a-1,b-1) for (a,b) in M if a!=0],4) for M in pm(range(4))]
    print('r=4 k=1 p=%d: dim (D_{4,J}) = %d   (Q_1(5)=36 ; formula 12h^2+6h+1 at h=3/2 gives 37)'%(p,dim(R1.ideal(DJ,p))))
print('time %.1fs'%(time.time()-t0))
