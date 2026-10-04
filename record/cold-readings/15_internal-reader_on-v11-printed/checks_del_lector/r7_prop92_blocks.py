# R7 (Grepy Tinta): Proposition 9.2 from the literal psi_J; Lemma 9.10; blocks per colouring. Own code.
import sys, itertools, time
import numpy as np
from collections import defaultdict, Counter
from math import comb, factorial
from fractions import Fraction as Fr
src=open('checks/r2_literal.py').read().split("print('== P2.5")[0]
exec(src)     # matchings, psi, flat, ideal_dim_p2, ideal_dim_odd
def Nr(r,n):
    I0=[Fr(1,factorial(i//2)**2) if i%2==0 else Fr(0) for i in range(n+1)]
    def mul(a,b):
        c=[Fr(0)]*(n+1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                if i+j<=n: c[i+j]+=x*y
        return c
    s=[Fr(1,factorial(i)) for i in range(n+1)]
    for _ in range((r-1)//2): s=mul(s,I0)
    return int(s[n]*factorial(n))
def Qodd(n,q):   # n-tuples in mu_q\{1}, q odd, that split
    if n%2: return 0
    I0=[Fr(1,factorial(i//2)**2) if i%2==0 else Fr(0) for i in range(n+1)]
    s=[Fr(1)]+[Fr(0)]*n
    for _ in range((q-1)//2):
        c=[Fr(0)]*(n+1)
        for i,x in enumerate(s):
            for j,y in enumerate(I0):
                if i+j<=n: c[i+j]+=x*y
        s=c
    return int(s[n]*factorial(n))
def rref2(M):
    M=M.copy()%2; nr,nc=M.shape; rr=0; piv=[]
    for c in range(nc):
        if rr==nr: break
        nz=np.flatnonzero(M[rr:,c])
        if nz.size==0: continue
        i=rr+int(nz[0])
        if i!=rr: M[[rr,i]]=M[[i,rr]]
        colv=M[:,c].copy(); colv[rr]=0
        nzr=np.flatnonzero(colv)
        if nzr.size: M[nzr]^=M[rr]
        piv.append(c); rr+=1
    return M[:rr],piv
t0=time.time()
print('== P7.1 / P7.2: Proposition 9.2 ==')
def polymul_trunc(A,B,q):   # arrays of shape (q,)*n over F_2, product mod s_i^q
    n=A.ndim; C=np.zeros_like(A)
    for e in zip(*np.nonzero(B)):
        sl_src=tuple(slice(0,q-x) for x in e); sl_dst=tuple(slice(x,q) for x in e)
        C[sl_dst]^=A[sl_src]
    return C
def prop92(k,q):
    n1=2*k+1; Js=list(matchings(range(n1+1)))
    # change of basis t^nu -> (1+s)^nu over F_2 : matrix T[j,e]=C(e,j) mod 2, applied on every axis
    T=np.array([[comb(e,j)%2 for e in range(q)] for j in range(q)],dtype=np.int64)
    def to_s(A):
        for ax in range(n1): A=np.moveaxis(np.tensordot(T,A,axes=([1],[ax])),0,ax)%2
        return A.astype(np.uint8)
    def mono(e):
        A=np.zeros((q,)*n1,dtype=np.uint8); A[tuple(e)]=1; return A
    def var(i): 
        e=[0]*n1; e[i-1]=1; return mono(e)
    ok_step1=True; ok_lead=True; ok_YD=True
    gens_s=[]; Lforms=[]; DJs=[]
    Y=np.zeros((q,)*n1,dtype=np.uint8); Y[(1,)*n1]=1
    deg=np.indices((q,)*n1).sum(axis=0)
    for J in Js:
        lit=to_s(psi(J,q,n1)%2)
        # Step 1 formula, L_J and Y*D_J computed directly in the s-ring
        F=mono([0]*n1); L=mono([0]*n1); D=mono([0]*n1)
        for (j,kk) in J:
            F=polymul_trunc(F,var(kk),q); L=polymul_trunc(L,var(kk),q)
            if j!=0:
                base=(var(j)+var(kk)+polymul_trunc(var(j),var(kk),q))%2; lin=(var(j)+var(kk))%2
                for _ in range(q-1): F=polymul_trunc(F,base,q); L=polymul_trunc(L,lin,q)
                Dp=np.zeros((q,)*n1,dtype=np.uint8)
                for w in range(q-1):
                    e=[0]*n1; e[j-1]=w; e[kk-1]=q-2-w; Dp[tuple(e)]^=1
                D=polymul_trunc(D,Dp,q)
        if not np.array_equal(lit,F): ok_step1=False
        dmin=deg[lit>0].min() if lit.any() else None
        lead=np.where(deg==dmin,lit,0) if dmin is not None else lit
        if not np.array_equal(lead,L): ok_lead=False
        YD=polymul_trunc(Y,D,q)
        if not np.array_equal(L,YD): ok_YD=False
        gens_s.append(lit); Lforms.append(L)
    # order of the s-monomials: by degree ascending
    order=np.argsort(deg.reshape(-1),kind='stable'); degs=deg.reshape(-1)[order]
    def closure(gens):
        Lr=q**n1; basisM=np.zeros((0,Lr),dtype=np.uint8); pivs=[]; queue=[]
        def reduce_insert(v):
            nonlocal basisM,pivs
            if pivs:
                coef=v[pivs]
                if coef.any(): v=(v^ (coef.astype(np.int64)@basisM.astype(np.int64)%2).astype(np.uint8))
            nz=np.flatnonzero(v)
            if nz.size==0: return None
            h=int(nz[0])
            if basisM.shape[0]:
                col=basisM[:,h].copy(); rows=np.flatnonzero(col)
                if rows.size: basisM[rows]^=v
            basisM=np.vstack([basisM,v[None,:]]); pivs.append(h); return v
        def mulvar(v,i):   # multiply by s_i, in the permuted coordinates
            A=np.zeros((q,)*n1,dtype=np.uint8); A.reshape(-1)[order]=v
            Bm=np.zeros_like(A); sl_src=[slice(None)]*n1; sl_dst=[slice(None)]*n1
            sl_src[i]=slice(0,q-1); sl_dst[i]=slice(1,q); Bm[tuple(sl_dst)]=A[tuple(sl_src)]
            return Bm.reshape(-1)[order]
        for g_ in gens:
            v=reduce_insert(g_.reshape(-1)[order].copy())
            if v is not None: queue.append(v)
        while queue:
            v=queue.pop()
            for i in range(n1):
                w=reduce_insert(mulvar(v,i))
                if w is not None: queue.append(w)
        # the stored rows are in reduced echelon form; pivot = lowest-degree monomial of the row
        hf=Counter(int(degs[h]) for h in pivs)
        return len(pivs),[hf[d] for d in sorted(hf)],min(hf) if hf else None
    dI,hfI,d0=closure(gens_s); dL,hfL,d0L=closure(Lforms)
    print('(k,q)=(%d,%d): Step1 formula: %s ; lowest component = L_J: %s ; L_J = Y*D_J: %s ; dim I=%d ; dim (L_J)B=%d ; N_{q-1}(2k+2)=%d'%(k,q,ok_step1,ok_lead,ok_YD,dI,dL,Nr(q-1,2*k+2)))
    print('    Hilbert function of in(I) from degree %s: %s'%(d0,hfI)); print('    Hilbert function of (L_J)B from degree %s: %s  equal: %s  (%.1fs)'%(d0L,hfL,hfI==hfL and d0==d0L,time.time()-t0)); sys.stdout.flush()
for (k,q) in [(1,4),(2,4),(1,8),(1,16)]: prop92(k,q)
print('== P7.3: Lemma 9.10, 0 not in C_1 ==')
def M_ideal(q,kp):
    n=2*kp
    gens=[]
    for P in matchings(range(1,n+1)):
        A=np.zeros((q,)*n,dtype=np.int64); A[(0,)*n]=1
        for (i,l) in P:
            A=np.roll(A,1,axis=l-1)-A
            Bm=np.zeros_like(A)
            for c in range(q): Bm+=np.roll(np.roll(A,c,axis=i-1),c,axis=l-1)
            A=Bm
        gens.append(flat(A,n))
    return ideal_dim_p2(gens,q,n)
for (q,kp) in [(2,1),(2,2),(2,3),(4,1),(4,2),(4,3),(8,1),(8,2)]:
    print('q=%d k\'=%d: dim M=%d   N_{q-1}(2k\')=%d'%(q,kp,M_ideal(q,kp),Nr(q-1,2*kp))); sys.stdout.flush()
print('== P7.4 / P7.5: blocks per colouring, r\'=2, odd p ==')
def per_colouring(k,m,p,drop=None):
    q=m//2; n1=2*k+1; Js=list(matchings(range(n1+1)))
    if drop is not None: Js=[J for i,J in enumerate(Js) if i!=drop]
    psis=[psi(J,m,n1)%p for J in Js]
    L=q**n1; idx=np.arange(L)
    shifts=[]
    for i in range(n1):
        s=q**i; dig=(idx//s)%q
        shifts.append((idx[dig<q-1],idx[dig<q-1]+s))
    res=[]
    for c in itertools.product((1,-1),repeat=n1):
        gens=[]
        for A in psis:
            B=A
            for ax in range(n1):
                Tm=np.array([[comb(e,j)*pow(c[ax],e-j,p)%p for e in range(m)] for j in range(q)],dtype=np.int64)
                B=np.moveaxis(np.tensordot(Tm,B,axes=([1],[ax])),0,ax)%p
            gens.append(np.transpose(B,axes=list(range(n1-1,-1,-1))).reshape(-1))
        rows=[]; pivset={}
        def insert(v):
            v=v%p
            while True:
                nz=np.flatnonzero(v)
                if nz.size==0: return None
                h=int(nz[0]); j=pivset.get(h)
                if j is None:
                    v=(v*pow(int(v[h]),-1,p))%p; pivset[h]=len(rows); rows.append(v); return v
                v=(v-int(v[h])*rows[j])%p
        queue=[]
        for g_ in gens:
            r_=insert(g_.astype(np.int64))
            if r_ is not None: queue.append(r_)
        while queue:
            v=queue.pop()
            for (src_,dst_) in shifts:
                w=np.zeros(L,dtype=np.int64); w[dst_]=v[src_]
                r_=insert(w)
                if r_ is not None: queue.append(r_)
        c0=1
        for x in c: c0*=x
        col=(c0,)+c; n_minus=col.count(-1); n_plus=col.count(1)
        pred=Qodd(n_plus,q)*Nr(q,n_minus)
        res.append((c,len(rows),pred))
    return res
for (k,m,p) in [(1,6,3),(2,6,3),(1,10,5),(1,14,7),(1,18,3)]:
    res=per_colouring(k,m,p); bad=[x for x in res if x[1]!=x[2]]
    by=Counter()
    for c,d,pr in res: by[(((1,)+c).count(1) if False else None)]+=0
    allm=[x for x in res if all(v==-1 for v in x[0])][0]; allp=[x for x in res if all(v==1 for v in x[0])][0]
    print('(k,m,p)=(%d,%d,%d): colourings=%d  mismatches=%d  sum of dims=%d  | all -1: dim=%d (N_q(2k+2)=%d) ; all +1: dim=%d (Q_k(q)=%d)  (%.1fs)'%(k,m,p,len(res),len(bad),sum(x[1] for x in res),allm[1],Nr(m//2,2*k+2),allp[1],Qodd(2*k+2,m//2),time.time()-t0)); sys.stdout.flush()
    for x in bad[:5]: print('   MISMATCH',x)
res=per_colouring(1,6,3,drop=0)
print('control (1,6,3), first matching removed: (colouring, dim, N_1*N_-1):',[(c,d,pr) for c,d,pr in res],' -> dims below the count in %d of %d colourings'%(sum(1 for c,d,pr in res if d<pr),len(res)))
print('time %.1fs'%(time.time()-t0))
