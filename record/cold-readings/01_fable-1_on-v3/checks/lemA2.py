# Exact (integer) check of Lemma A.8 (P),(B),(A),(V), Lemma A.9 and Lemma A.10 (multiplied by 2), own truncated-series code.
import random, itertools
# polys: dict exp-tuple -> int over variables indexed 0..nv-1 ; series in t: list of polys
def padd(a,b,c=1):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,0)+c*v
    return {k:v for k,v in r.items() if v}
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def smul(S1,S2,N):
    R=[{} for _ in range(N+1)]
    for i,a in enumerate(S1):
        if not a: continue
        for j,b in enumerate(S2):
            if i+j>N: break
            if b: R[i+j]=padd(R[i+j],pmul(a,b))
    return R
def var(i,nv,pw=1):
    k=[0]*nv; k[i]=pw; return {tuple(k):1}
def one(nv): return {tuple([0]*nv):1}
def lin_series(i,nv,sign,N):  # 1 + sign*x_i t
    S=[{} for _ in range(N+1)]; S[0]=one(nv)
    if N>=1: S[1]=var(i,nv) if sign==1 else {tuple(var(i,nv).keys())[0]:-1}
    return S
def inv_series(i,nv,sign,N):  # (1 + sign*x_i t)^{-1} = sum (-sign x_i)^j t^j
    S=[]
    for j in range(N+1):
        S.append({tuple(var(i,nv,j).keys())[0]:(-sign)**j})
    return S
def Theta(nv,L,A,B,s,q):
    P=[x for x in L if x not in A and x not in B]
    D=len(A)*(q-1)+len(P)+1-s
    if D<0: return {}
    S=[{} for _ in range(D+1)]; S[0]=one(nv)
    for x in P: S=smul(S,lin_series(x,nv,-1,D),D)
    for a in A:
        S=smul(S,lin_series(a,nv,-1,D),D); S=smul(S,inv_series(a,nv,1,D),D)
    return S[D]
def E(nv,X,sign,N):
    S=[{} for _ in range(N+1)]; S[0]=one(nv)
    for x in X: S=smul(S,lin_series(x,nv,sign,N),N)
    return S
def zpow(nv,zi,p,f): return pmul(var(zi,nv,p),f) if p>0 else f
random.seed(7)
for q in [3,5]:
  for trial in range(8):
    n=random.randint(1,4); nv=n+1; L=list(range(n)); z=n; Lp=L+[z]
    A=[x for x in L if random.random()<0.4]; B=[x for x in L if x not in A and random.random()<0.4]
    s=random.randint(-2,6)
    assert padd(Theta(nv,Lp,A,B,s,q), padd(Theta(nv,L,A,B,s-1,q), zpow(nv,z,1,Theta(nv,L,A,B,s,q)),-1),-1)=={}, "P"
    assert padd(Theta(nv,Lp,A,B+[z],s,q),Theta(nv,L,A,B,s,q),-1)=={}, "B"
    rhs=Theta(nv,L,A,B,s-q+1,q)
    for i in range(1,s+(n+1)*q+3):
        rhs=padd(rhs, zpow(nv,z,i,Theta(nv,L,A,B,s-q+1+i,q)), 2*(-1)**i)
    assert padd(Theta(nv,Lp,A+[z],B,s,q),rhs,-1)=={}, "A"
    if s<=0:
        th=Theta(nv,L,A,B,s,q)
        if A: assert all(max(k[a] for a in A)>=q for k in th), "V"
        else: assert th=={}, "V0"
    for a in range(0,3):
        rhs=Theta(nv,Lp,A,B+[z],s-a,q)
        for i in range(1,a+1): rhs=padd(rhs, zpow(nv,z,i-1,Theta(nv,Lp,A,B,s-a+i,q)),-1)
        assert padd(zpow(nv,z,a,Theta(nv,L,A,B,s,q)),rhs,-1)=={}, "A9"
  print(f"q={q}: A.8 (P)(B)(A)(V) and A.9 exact: OK on 8 random instances")
# A.10, multiplied by 2
for q in [3,5]:
  for trial in range(6):
    n=random.randint(2,5); nv=n+1; L=list(range(n)); z=n; Lp=L+[z]
    r=random.randint(0,n//2); A=L[:r]; B=L[r:2*r]; P=L[2*r:]
    c=random.randint(-1,4); M=r*(q-1)+len(P)+1-c; ell=random.randint(0,2)
    N=max(M,0)+1
    H=[{} for _ in range(N+1)]; H[0]=one(nv)
    for a in A: H=smul(H,inv_series(a,nv,1,N),N)
    for b in B: H=smul(H,inv_series(b,nv,-1,N),N)
    h=lambda m: H[m] if 0<=m<=N else {}
    Ep=E(nv,Lp,1,n+1)
    Om={}
    for j in range(1,n+2,2):
        Om=padd(Om, zpow(nv,z,ell,pmul(Ep[j],h(M-j))))
        Om=padd(Om, zpow(nv,z,ell+1,pmul(Ep[j],h(M-1-j))),-1)
    lhs=zpow(nv,z,ell+1,Theta(nv,L,A,B,c+1,q))
    # 2*lhs - (2*Om - z^ell((-1)^M Theta(B;A) - Theta(A;B))) must be divisible by z^{ell+2}
    d=padd(pmul({tuple([0]*nv):2},lhs), pmul({tuple([0]*nv):2},Om), -1)
    d=padd(d, zpow(nv,z,ell,padd(pmul({tuple([0]*nv):(-1)**M},Theta(nv,L,B,A,c,q)),Theta(nv,L,A,B,c,q),-1)))
    assert all(k[z]>=ell+2 for k in d), ("A10",q,n,r,c,ell,[k for k in d if k[z]<ell+2][:3])
  print(f"q={q}: A.10 exact (×2): OK on 6 random instances")
