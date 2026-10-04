# R4 (Grepy Tinta): the bipartite ideals of §7 at an even box. Own code.
import sys, itertools, time
import numpy as np
from collections import defaultdict, Counter
from math import comb
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
class Ring:
    def __init__(self,nv,q):
        self.nv=nv; self.q=q; self.monos=defaultdict(list)
        for e in itertools.product(range(q),repeat=nv): self.monos[sum(e)].append(e)
        self.pos={d:{e:i for i,e in enumerate(L)} for d,L in self.monos.items()}
        self.maxdeg=nv*(q-1); self.shift={}
        for d in range(self.maxdeg):
            for j in range(nv):
                src=[];dst=[]
                for i,e in enumerate(self.monos[d]):
                    if e[j]<q-1:
                        f=list(e); f[j]+=1; src.append(i); dst.append(self.pos[d+1][tuple(f)])
                self.shift[(d,j)]=(np.array(src,dtype=int),np.array(dst,dtype=int))
    def ideal_dim(self,polys,p):
        gens=defaultdict(list)
        for P in polys:
            P={k:v%p for k,v in P.items() if v%p}
            if not P: continue
            degs={sum(e) for e in P}; assert len(degs)==1
            d=degs.pop(); v=np.zeros(len(self.monos[d]),dtype=np.int64)
            for e,c in P.items(): v[self.pos[d][e]]=c
            gens[d].append(v)
        prev=None; tot=0
        for d in range(self.maxdeg+1):
            rows=list(gens.get(d,[]))
            if prev is not None and len(prev):
                for j in range(self.nv):
                    s_,d_=self.shift[(d-1,j)]
                    W=np.zeros((prev.shape[0],len(self.monos[d])),dtype=np.int64); W[:,d_]=prev[:,s_]; rows.extend(list(W))
            B=rref(np.array(rows,dtype=np.int64),p)[0] if rows else np.zeros((0,len(self.monos[d])),dtype=np.int64)
            tot+=B.shape[0]; prev=B
        return tot
def partitions(n,maxpart=None):
    if maxpart is None: maxpart=n
    if n==0: yield (); return
    for a in range(min(n,maxpart),0,-1):
        for rest in partitions(n-a,a): yield (a,)+rest
def St(l,t): return sum(l[:t])
def leq(a,b):
    L=max(len(a),len(b),1); return all(St(a,t)<=St(b,t) for t in range(1,L+1))
def BPar(q,al,be):
    out=[]
    for s in range(0,al+be+1):
        for sp in range(0,s+1):
            sm=s-sp
            if sp-sm!=al-be: continue
            for lp in partitions(sp):
                for lm in partitions(sm):
                    if len(lp)+len(lm)<=q: out.append((lp,lm))
    return out
def pleq(a,b): return leq(a[0],b[0]) and leq(a[1],b[1])
def downsets(S):
    res=[]
    for bits in range(1,2**len(S)):
        L=[S[i] for i in range(len(S)) if bits>>i&1]; Ls=set(L)
        if all((mu in Ls) for lam in L for mu in S if pleq(mu,lam)): res.append(frozenset(L))
    return res
def shape(xi,eta,q):
    X=Counter(xi); Y=Counter(eta)
    lp=tuple(sorted([X[u]-Y[u] for u in range(q) if X[u]>Y[u]],reverse=True))
    lm=tuple(sorted([Y[u]-X[u] for u in range(q) if Y[u]>X[u]],reverse=True))
    return (lp,lm)
def cols(lam): return [sum(1 for x in lam if x>=c) for c in range(1,(lam[0] if lam else 0)+1)]
def choose_blocks(S,sizes):
    if not sizes:
        if not S: yield []
        return
    for B in itertools.combinations(S,sizes[0]):
        rest=[x for x in S if x not in B]
        for more in choose_blocks(rest,sizes[1:]): yield [B]+more
def pmul(a,b,q):
    d={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2))
            if max(k)>=q: continue
            d[k]=d.get(k,0)+v1*v2
    return {k:v for k,v in d.items() if v}
def lin_pow(nv,i,l,q):   # (x_i - z_l)^(q-1), variables: x's are 0..al-1, z's are al..al+be-1 (i,l are absolute positions)
    d={}
    for t in range(q):
        k=[0]*nv; k[i]+=q-1-t; k[l]+=t; d[tuple(k)]=comb(q-1,t)*(-1)**t
    return d
def vander(nv,B,q):
    B=sorted(B); P={tuple([0]*nv):1}
    for a in range(len(B)):
        for b in range(a+1,len(B)):
            f={}
            k=[0]*nv; k[B[b]]=1; f[tuple(k)]=1
            k=[0]*nv; k[B[a]]=1; f[tuple(k)]=-1
            P=pmul(P,f,q)
    return P
def patterns(q,al,be,lam,only_identity=False):
    lp,lm=lam; nv=al+be; npairs=al-sum(lp); A=list(range(al)); Bz=list(range(al,al+be)); out=[]
    for UA in itertools.combinations(A,npairs):
        for UB in itertools.combinations(Bz,npairs):
            restA=[x for x in A if x not in UA]; restB=[x for x in Bz if x not in UB]
            bA=list(choose_blocks(restA,cols(lp))); bB=list(choose_blocks(restB,cols(lm)))
            perms=[UB] if only_identity else itertools.permutations(UB)
            for perm in perms:
                DP={tuple([0]*nv):1}
                for i,l in zip(UA,perm): DP=pmul(DP,lin_pow(nv,i,l,q),q)
                for BA in bA:
                    PA=DP
                    for B in BA: PA=pmul(PA,vander(nv,B,q),q)
                    for BB in bB:
                        P=PA
                        for B in BB: P=pmul(P,vander(nv,B,q),q)
                        out.append(P)
    return out
def Nbal(a,q):
    return sum(1 for xi in itertools.product(range(q),repeat=a) for eta in itertools.product(range(q),repeat=a) if Counter(xi)==Counter(eta)) if q**(2*a)<=300000 else None
def cell(q,al,be,p,verbose=True):
    S=BPar(q,al,be); R=Ring(al+be,q)
    pts=Counter(shape(xi,eta,q) for xi in itertools.product(range(q),repeat=al) for eta in itertools.product(range(q),repeat=be))
    assert set(pts)<=set(S), 'a point has a shape outside BPar'
    pat={lam:patterns(q,al,be,lam) for lam in S}
    DS=downsets(S); eq=0; gt=0; lt=0
    for L in DS:
        polys=[P for lam in L for P in pat[lam]]
        d=R.ideal_dim(polys,p); z=sum(pts[lam] for lam in L)
        if d==z: eq+=1
        elif d>z: gt+=1
        else: lt+=1; print('   !! dim<|Z|',q,al,be,p,sorted(L),d,z)
    root=None
    if al==be: root=frozenset({((),())})
    elif al==be+1: root=frozenset({((1,),())})
    rd=None
    if root in DS:
        rd=(R.ideal_dim([P for lam in root for P in pat[lam]],p), sum(pts[lam] for lam in root))
    print('q=%d (alpha,beta)=(%d,%d) p=%d: |BPar|=%d down-sets=%d  equal=%d  dim>|Z|=%d  dim<|Z|=%d  root (dim,|Z|)=%s'%(q,al,be,p,len(S),len(DS),eq,gt,lt,rd)); sys.stdout.flush()
t0=time.time()
print('== P4.0 regression q=3 =='); cell(3,2,2,3); cell(3,2,2,10007); cell(3,1,1,3); cell(3,2,1,3)
print('== P4.1/P4.2 even box over F_2 ==')
for (q,al,be) in [(2,1,0),(2,1,1),(2,2,1),(2,2,2),(2,3,2),(2,3,3),(2,4,3),(4,1,1),(4,2,1),(4,2,2),(4,3,2),(8,1,1),(8,2,1)]:
    cell(q,al,be,2)
print('== P4.3 q=4 over F_5 ==')
for (al,be) in [(1,1),(2,1),(2,2)]: cell(4,al,be,5)
print('== P4.5 q=4 over F_3 (hypothesis of Theorem C fails) ==')
for (al,be) in [(1,1),(2,1),(2,2)]: cell(4,al,be,3)
print('== q=6 over F_7 (binomials non-zero) and over F_2 (C(5,1)=5 odd, C(5,2)=10 even: hypothesis fails) ==')
for p_ in (7,2):
    for (al,be) in [(1,1),(2,1)]: cell(6,al,be,p_)
print('== P4.4 control: one bijection only, (a,q)=(2,2), F_2 ==')
R=Ring(4,2); print('   identity only: dim =',R.ideal_dim(patterns(2,2,2,((),()),only_identity=True),2),' all of S_2: dim =',R.ideal_dim(patterns(2,2,2,((),())),2),' N_bal(2,2)=',Nbal(2,2))
R=Ring(4,4); print('   q=4: identity only: dim =',R.ideal_dim(patterns(4,2,2,((),()),only_identity=True),2),' all of S_2: dim =',R.ideal_dim(patterns(4,2,2,((),())),2),' N_bal(2,4)=',Nbal(2,4))
print('time %.1fs'%(time.time()-t0))
