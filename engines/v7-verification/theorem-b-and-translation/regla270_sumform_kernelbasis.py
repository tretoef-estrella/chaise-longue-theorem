# Independent route: (D_J)C = tensor_p K_p (x) Lambda_{k0}, K_p basis D(y_j,y_k)*y_j^i (i=0..q-2).
# exact rank mod 3 degree by degree; |Gamma_K| by enumeration.
import itertools, numpy as np, sys
p=3; q=int(sys.argv[1]); k=int(sys.argv[2]); drop=sys.argv[3] if len(sys.argv)>3 else ""
n=q-1; N=2*k+2; nv=2*k+1
def matchings(s):
    if not s: yield []; return
    a=s[0]
    for i in range(1,len(s)):
        for m in matchings(s[1:i]+s[i+1:]): yield [(a,s[i])]+m
allM=list(matchings(list(range(N))))
dropped=[tuple(sorted(tuple(x) for x in eval(d))) for d in drop.split(";") if d]
K=[M for M in allM if tuple(sorted(M)) not in dropped]
print("q",q,"k",k,"|K|",len(K),"dropped",dropped)
def pmul(P,Q):
    R={}
    for e,c in P.items():
        for f,d in Q.items():
            g=tuple(x+y for x,y in zip(e,f))
            if max(g)>=n: continue
            R[g]=(R.get(g,0)+c*d)%p
    return {e:c for e,c in R.items() if c}
def mono(v,ex): e=[0]*nv; e[v]=ex; return {tuple(e):1}
def Dpoly(a,b): # variables indices 1..nv -> positions a-1,b-1
    P={}
    for u in range(q-1):
        e=[0]*nv; e[a-1]+=u; e[b-1]+=q-2-u
        P[tuple(e)]=((-1)**u)%p
    return P
bydeg={}
for M in K:
    k0=[b for (a,b) in M if a==0][0]
    pairs=[(a,b) for (a,b) in M if a!=0]
    facs=[[pmul(Dpoly(a,b),mono(a-1,i)) for i in range(n)] for (a,b) in pairs]
    facs.append([mono(k0-1,e) for e in range(n)])
    for combo in itertools.product(*facs):
        P={tuple([0]*nv):1}
        for f in combo:
            P=pmul(P,f)
            if not P: break
        if P:
            d=sum(next(iter(P)))
            bydeg.setdefault(d,[]).append(P)
def rank_mod3(A):
    A=A.copy()%3; r=0; rows,cols=A.shape
    for c in range(cols):
        nz=np.nonzero(A[r:,c])[0]
        if len(nz)==0: continue
        i=r+nz[0]; A[[r,i]]=A[[i,r]]
        if A[r,c]==2: A[r]=(A[r]*2)%3
        f=A[:,c].copy(); f[r]=0
        A=(A-np.outer(f,A[r]))%3
        r+=1
        if r==rows: break
    return r
tot=0; ranks=[]
for d in sorted(bydeg):
    polys=bydeg[d]; mons=sorted({e for P in polys for e in P}); ix={e:i for i,e in enumerate(mons)}
    A=np.zeros((len(polys),len(mons)),dtype=np.int64)
    for r,P in enumerate(polys):
        for e,c in P.items(): A[r,ix[e]]=c
    rk=rank_mod3(A); ranks.append(rk); tot+=rk
print("graded ranks",ranks); print("dim (D_J:J in K)C =",tot)
# Gamma_K: exponents a_i in Z/q, nonzero, a_0 = -sum
G=0
for a in itertools.product(range(1,q),repeat=nv):
    x=(( -sum(a))%q,)+a
    if x[0]==0: continue
    for M in K:
        if all((x[i]+x[j])%q==0 for (i,j) in M if i!=0):
            G+=1; break
print("|Gamma_K| =",G)
