# R3 (Grepy Tinta): Theorem 8.11 built from Definition 8.6. Own code.
import sys, itertools, time
import numpy as np
from collections import defaultdict, Counter
r=int(sys.argv[1]); MMAX=int(sys.argv[2]); PRIMES=[int(x) for x in sys.argv[3].split(',')] if len(sys.argv)>3 else [2,3,10007]
T0ONLY = (len(sys.argv)>4 and sys.argv[4]=='t0')
h=(r-1)//2
# ---------- polynomials: dict {exps tuple: int}, variables 0..m-1 (0 <-> y_1) ----------
def padd(a,b,c=1):
    d=dict(a)
    for k,v in b.items():
        d[k]=d.get(k,0)+c*v
        if d[k]==0: del d[k]
    return d
def pmul(a,b):
    d={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2))
            if max(k)>=r: continue
            d[k]=d.get(k,0)+v1*v2
    return {k:v for k,v in d.items() if v}
def mono(m,i,e):
    k=[0]*m; k[i]=e; return {tuple(k):1}
def one(m): return {tuple([0]*m):1}
def Dpoly(m,a,b):
    d={}
    for u in range(r):
        k=[0]*m; k[a]+=u; k[b]+=r-1-u; d[tuple(k)]=(-1)**u
    return d
def Dminus(m,a,b):
    d={}
    for u in range(r-1):
        k=[0]*m; k[a]+=u; k[b]+=r-2-u; d[tuple(k)]=(-1)**u
    return d
def vander(m,B):
    B=sorted(B); P=one(m)
    for i in range(len(B)):
        for j in range(i+1,len(B)):
            P=pmul(P,padd(mono(m,B[j],1),mono(m,B[i],1),-1))
    return P
def pfaff(A):
    # A: dict {(i,j): poly} for i<j over indices 0..n-1 (n even), expansion along the first index
    def rec(idx):
        if not idx: return None  # stands for 1
        i=idx[0]; tot={}
        for pos in range(1,len(idx)):
            j=idx[pos]; a=A.get((i,j))
            if not a: continue
            sub=rec(idx[1:pos]+idx[pos+1:])
            term=a if sub is None else pmul(a,sub)
            tot=padd(tot,term,(-1)**(pos-1))
        return tot
    return rec
def pf_bordered(m,Nset,E):
    Nl=sorted(Nset); E=sorted(E); n=len(Nl); s=len(E)
    if (n+s)%2: return {}
    A={}
    for a in range(n):
        for b in range(a+1,n): A[(a,b)]=Dminus(m,Nl[a],Nl[b])
        for kk in range(s): A[(a,n+kk)]=mono(m,Nl[a],E[kk])
    if n+s==0: return one(m)
    res=pfaff(A)(tuple(range(n+s)))
    return res
def Eset(l): return [r-1] if l==0 else list(range(l-1))
# ---------- combinatorics of shapes ----------
def partitions(n,maxparts,maxpart=None):
    if maxpart is None: maxpart=n
    if n==0: yield (); return
    if maxparts==0: return
    for a in range(min(n,maxpart),0,-1):
        for rest in partitions(n-a,maxparts-1,a): yield (a,)+rest
def Pn(n):
    if n<0: return []
    return [lam for s in range(n%2,n+1,2) for lam in partitions(s,h)]
def Sh(m): return [(lam,0) for lam in Pn(m)]+[(lam,1) for lam in Pn(m-1)]
def St(lam,t): return sum(lam[:t])
def leq(a,b):
    L=max(len(a),len(b),1)
    return all(St(a,t)<=St(b,t) for t in range(1,L+1))
def minus(lam,j):
    l=list(lam); l[j]-=1; return tuple(sorted([x for x in l if x>0],reverse=True))
def plus(lam,j):
    l=list(lam); l[j]+=1; return tuple(sorted(l,reverse=True))
def is_interlaced(Lam,m):
    L0=[l for (l,d) in Lam if d==0]; L1=[l for (l,d) in Lam if d==1]
    S=set(Lam)
    for l in L0:
        for mu in Pn(m):
            if leq(mu,l) and (mu,0) not in S: return False
    for l in L1:
        for mu in Pn(m-1):
            if leq(mu,l) and (mu,1) not in S: return False
    return True
def satisfies_D2(Lam):
    S=set(Lam)
    for (nu,d) in Lam:
        for j in range(len(nu)):
            if (minus(nu,j),1-d) not in S: return False
    return True
def shape_of(M):
    c=Counter(M); parts=sorted([abs(c[u]-c[-u]) for u in range(1,h+1) if c[u]!=c[-u]],reverse=True)
    return (tuple(parts),c[0]%2)
Tvals=list(range(-h,h+1))
def options_list(mu,d):   # the list of Lemma 8.3
    l=len(mu)
    return [(minus(mu,j),d) for j in range(l)]+[(mu,1-d)]+[(tuple(mu)+(1,),d)]*(r-1-2*l)+[(plus(mu,j),d) for j in range(l-1,-1,-1)]
# ---------- patterns (Definition 8.6) ----------
def perfect_matchings(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for i in range(1,len(S)):
        for M in perfect_matchings(S[1:i]+S[i+1:]): yield [(a,S[i])]+M
def choose_blocks(S,sizes):
    if not sizes:
        if not S: yield []
        return
    for B in itertools.combinations(S,sizes[0]):
        rest=[x for x in S if x not in B]
        for more in choose_blocks(rest,sizes[1:]): yield [B]+more
def cols(lam):
    return [sum(1 for x in lam if x>=c) for c in range(1,(lam[0] if lam else 0)+1)]
_pfcache={}
def pattern_products(m,I,shape,t0only=False):
    # generator: yields the product of every pattern of `shape` on I (Definition 8.6)
    lam,d=shape; l=len(lam); cl=cols(lam); I=list(I)
    if d==0:
        npairs=(len(I)-sum(lam))//2
        for U in itertools.combinations(I,2*npairs):
            rest=[x for x in I if x not in U]
            blocks=list(choose_blocks(rest,cl))
            for Mt in perfect_matchings(U):
                DP=one(m)
                for (a,b) in Mt: DP=pmul(DP,Dpoly(m,a,b))
                for Bl in blocks:
                    P=DP
                    for B in Bl: P=pmul(P,vander(m,B))
                    yield P
    else:
        tot=(len(I)-1-sum(lam))//2
        for t in range(0,tot+1):
            if t0only and t>0: break
            npairs=tot-t; b0=l+1+2*t
            for U in itertools.combinations(I,2*npairs):
                rest=[x for x in I if x not in U]
                for B0 in itertools.combinations(rest,b0):
                    rest2=[x for x in rest if x not in B0]
                    PF=pf_bordered(m,B0,Eset(l))
                    blocks=list(choose_blocks(rest2,cl[1:]))
                    for Mt in perfect_matchings(U):
                        DP=PF
                        for (a,b) in Mt: DP=pmul(DP,Dpoly(m,a,b))
                        for Bl in blocks:
                            P=DP
                            for B in Bl: P=pmul(P,vander(m,B))
                            yield P
# ---------- linear algebra mod p, graded ----------
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
    def __init__(self,nv):
        self.nv=nv
        self.monos=defaultdict(list)
        for e in itertools.product(range(r),repeat=nv): self.monos[sum(e)].append(e)
        # order inside a degree: exponent of variable 0 descending first (for the slices), then lexicographic
        for d in self.monos: self.monos[d].sort(key=lambda e:(-e[0],e) if nv else e)
        self.pos={d:{e:i for i,e in enumerate(L)} for d,L in self.monos.items()}
        self.maxdeg=nv*(r-1)
        self.shift={}
        for d in range(self.maxdeg):
            for j in range(nv):
                src=[];dst=[]
                for i,e in enumerate(self.monos[d]):
                    if e[j]<r-1:
                        f=list(e); f[j]+=1; src.append(i); dst.append(self.pos[d+1][tuple(f)])
                self.shift[(d,j)]=(np.array(src,dtype=int),np.array(dst,dtype=int))
    def vec(self,P,p):
        d=sum(next(iter(P)))
        v=np.zeros(len(self.monos[d]),dtype=np.int64)
        for e,c in P.items(): v[self.pos[d][e]]=c%p
        return d,v
    def ideal(self,polys,p):
        # returns dict degree -> rref basis (rows) ; generators homogeneous
        gens=defaultdict(list)
        for P in polys:
            if not P: continue
            degs={sum(e) for e in P}; assert len(degs)==1, 'non-homogeneous generator'
            d,v=self.vec(P,p)
            if v.any(): gens[d].append(v)
        basis={}
        prev=None
        for d in range(self.maxdeg+1):
            rows=list(gens.get(d,[]))
            if prev is not None and len(prev):
                for j in range(self.nv):
                    src,dst=self.shift[(d-1,j)]
                    W=np.zeros((prev.shape[0],len(self.monos[d])),dtype=np.int64)
                    W[:,dst]=prev[:,src]
                    rows.extend(list(W))
            if rows:
                B,_=rref(np.array(rows,dtype=np.int64),p)
            else: B=np.zeros((0,len(self.monos[d])),dtype=np.int64)
            basis[d]=B; prev=B
        return basis
def _ideal_vecs(self,gens,p):
    basis={}; prev=None
    for d in range(self.maxdeg+1):
        rows=[np.asarray(v,dtype=np.int64)%p for v in gens.get(d,[])]
        if prev is not None and len(prev):
            for j in range(self.nv):
                src_,dst_=self.shift[(d-1,j)]
                W=np.zeros((prev.shape[0],len(self.monos[d])),dtype=np.int64)
                W[:,dst_]=prev[:,src_]
                rows.extend(list(W))
        if rows: B,_=rref(np.array(rows,dtype=np.int64),p)
        else: B=np.zeros((0,len(self.monos[d])),dtype=np.int64)
        basis[d]=B; prev=B
    return basis
Ring.ideal_vecs=_ideal_vecs
def dim_of(basis): return sum(B.shape[0] for B in basis.values())
RINGS={}
def ring(nv):
    if nv not in RINGS: RINGS[nv]=Ring(nv)
    return RINGS[nv]
PAT={}
def patterns(m,shape,t0only=False):
    key=(m,shape,t0only)
    if key not in PAT:
        R=ring(m); out=defaultdict(list); seen=set()
        for P in pattern_products(m,range(m),shape,t0only):
            if not P: continue
            degs={sum(e) for e in P}; assert len(degs)==1,'non-homogeneous pattern'
            d=degs.pop(); v=np.zeros(len(R.monos[d]),dtype=np.int32)
            for e,c in P.items(): v[R.pos[d][e]]=c
            kb=(d,v.tobytes())
            if kb in seen or (d,(-v).tobytes()) in seen: continue
            seen.add(kb); out[d].append(v)
        PAT[key]=out
    return PAT[key]
VB={}
def Vbasis(m,Lam,p,t0only=False,cache=True):
    key=(m,frozenset(Lam),p,t0only)
    if key in VB: return VB[key]
    gens=defaultdict(list)
    for sh in Lam:
        for d,L in patterns(m,sh,t0only).items(): gens[d].extend(L)
    B=ring(m).ideal_vecs(gens,p)
    B={d:M.astype(np.int16) for d,M in B.items()}
    if cache: VB[key]=B
    return B
def slices(m,basis,p):
    # W_j as graded subspaces of the ring in variables 1..m-1: dict j -> dict e -> list of vectors (over ring(m-1) monos of degree e)
    R=ring(m); R1=ring(m-1); W=defaultdict(lambda: defaultdict(list))
    for d,B in basis.items():
        if B.shape[0]==0: continue
        B2,piv=rref(B.copy(),p)   # columns already ordered by y_1-exponent descending
        for row,pc in zip(B2,piv):
            j=R.monos[d][pc][0]; e=d-j
            v=np.zeros(len(R1.monos[e]),dtype=np.int64)
            for i in np.flatnonzero(row):
                mon=R.monos[d][i]
                if mon[0]==j: v[R1.pos[e][mon[1:]]]=row[i]
            W[j][e].append(v)
    return W
def rank(rows,p,nc):
    if not rows: return 0
    return rref(np.array(rows,dtype=np.int64).reshape(len(rows),nc),p)[0].shape[0]
# ---------- main ----------
t00=time.time()
allS={m:Sh(m) for m in range(0,MMAX+1)}
points={m:Counter(shape_of(M) for M in itertools.product(Tvals,repeat=m)) for m in range(0,MMAX+1)}
def Zcount(m,Lam): return sum(points[m][s] for s in Lam)
IL={}; D1only={}
for m in range(0,MMAX+1):
    S=allS[m]; il=[]; d1=[]
    for bits in range(1,2**len(S)):
        Lam=frozenset(S[i] for i in range(len(S)) if bits>>i&1)
        if is_interlaced(Lam,m):
            if satisfies_D2(Lam): il.append(Lam)
            else: d1.append(Lam)
    IL[m]=il; D1only[m]=d1
    print('r=%d m=%d shapes=%d interlaced pairs=%d (D1)-not-(D2) pairs=%d'%(r,m,len(S),len(il),len(d1)))
fail=Counter(); tot=Counter()
for m in range(1,MMAX+1):
    # P3.1 combinatorics
    for Lam in IL[m]:
        # completions by brute force for every tail
        comp=defaultdict(set)
        Z=set(M for M in itertools.product(Tvals,repeat=m) if shape_of(M) in Lam)
        for Mp in itertools.product(Tvals,repeat=m-1):
            comp[shape_of(Mp)].add(sum(1 for y in Tvals if (y,)+Mp in Z))
        F={}
        for sg in allS[m-1]:
            tot['P1']+=1
            opts=options_list(*sg)
            inL=[o in Lam for o in opts]
            Fform=sum(inL)
            if comp[sg]!={Fform}: fail['P1 (8.5)']+=1
            if any(inL[i+1] and not inL[i] for i in range(len(inL)-1)): fail['chain']+=1
            F[sg]=Fform
        layers=[frozenset(sg for sg in allS[m-1] if F[sg]>i) for i in range(r)]
        for i,L in enumerate(layers):
            tot['layer']+=1
            if L and not (is_interlaced(L,m-1) and satisfies_D2(L)): fail['layer not interlaced']+=1
        if sum(Zcount(m-1,L) for L in layers)!=len(Z): fail['sum of layers']+=1
        # algebra
        for p in PRIMES:
            B=Vbasis(m,Lam,p,T0ONLY); dV=dim_of(B); tot['dim']+=1
            if dV<len(Z): fail['dim < |Z| (p=%d)'%p]+=1; print('  !! dim<|Z|',r,m,p,sorted(Lam),dV,len(Z))
            elif dV>len(Z): fail['dim > |Z| (p=%d)'%p]+=1; print('  dim>|Z|',r,m,p,sorted(Lam),dV,len(Z))
            if T0ONLY: continue
            W=slices(m,B,p); R1=ring(m-1)
            for i,L in enumerate(layers):
                j=r-1-i
                dW=sum(rank(W[j][e],p,len(R1.monos[e])) for e in list(W[j].keys()))
                tot['slice']+=1
                if dW!=Zcount(m-1,L): fail['dim W != |Z_layer|']+=1
                if not L: continue
                BL=Vbasis(m-1,L,p)
                okc=True; oklow=True
                for e,Bm in BL.items():
                    if Bm.shape[0]==0: continue
                    nc=len(R1.monos[e])
                    if rank(W[j][e]+list(Bm),p,nc)!=rank(W[j][e],p,nc): okc=False
                    if j>=1 and rank(W[j-1][e]+list(Bm),p,nc)!=rank(W[j-1][e],p,nc): oklow=False
                if not okc: fail['containment (Prop 8.10)']+=1; print('  !! containment fails',r,m,p,sorted(Lam),i)
                if j>=1:
                    tot['lowered']+=1
                    if not oklow: fail['CONTROL lowered slice fails (expected)']+=1
    # controls: (D1) not (D2)
    for Lam in D1only[m]:
        Z=Zcount(m,Lam)
        for p in PRIMES:
            dV=dim_of(Vbasis(m,Lam,p,T0ONLY,cache=False)); tot['D1notD2']+=1
            if dV!=Z: fail['CONTROL D1-not-D2 dim != |Z| (expected)']+=1
            if m==3 and r==3 and Lam==frozenset({((1,),0)}): print('  control {((1),0)} at (3,3), p=%d: dim=%d |Z|=%d'%(p,dV,Z))
    for kk in [kk for kk in VB if kk[0]<m]: del VB[kk]
    print('m=%d done (%.1fs)'%(m,time.time()-t00)); sys.stdout.flush()
print('TOTALS',dict(tot)); print('FAILURES/CONTROLS',dict(fail))
# roots
for m in range(1,MMAX+1,2):
    k=(m-1)//2; root=frozenset({((1,),0),((),1)})
    for p in PRIMES:
        B=Vbasis(m,root,p,T0ONLY)
        DJ=[]
        for c in range(m):
            for Mt in perfect_matchings([x for x in range(m) if x!=c]):
                P=one(m)
                for (a,b) in Mt: P=pmul(P,Dpoly(m,a,b))
                DJ.append(P)
        BJ=ring(m).ideal(DJ,p)
        same=all(B[d].shape==BJ[d].shape and (B[d].shape[0]==0 or rank(list(B[d])+list(BJ[d]),p,B[d].shape[1])==B[d].shape[0]) for d in B)
        W=slices(m,B,p) if not T0ONLY else None
        sl=[sum(rank(W[j][e],p,len(ring(m-1).monos[e])) for e in list(W[j].keys())) for j in range(r)] if W else None
        print('root r=%d m=%d p=%d: dim V_root=%d dim (D_J)=%d same ideal=%s |Z|=%d slices W_0..W_{r-1}=%s'%(r,m,p,dim_of(B),dim_of(BJ),same,Zcount(m,root),sl))
if r==3 and MMAX>=3:
    Lam=frozenset({((),1)})
    for p in PRIMES:
        print('Lambda={(empty,1)} at (3,3) p=%d: dim with all t = %d ; with t=0 only = %d ; |Z|=%d'%(p,dim_of(Vbasis(3,Lam,p,False)),dim_of(Vbasis(3,Lam,p,True)),Zcount(3,Lam)))
print('time %.1fs'%(time.time()-t00))
