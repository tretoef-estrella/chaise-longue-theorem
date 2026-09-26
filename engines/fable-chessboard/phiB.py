# minimal-degree lift of phi_ab on W_(1,1)(n) in the ansatz u^i b^j e_k(P) (coefficients constants), q given
import sys, numpy as np, itertools, time
from fq import Fq
from ansatz12 import Solver
n=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); T0=time.time()
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1,3])]
N=len(W); a,b=0,1; P=list(range(2,n)); f=n-2; deg=q+f-2; ml=F.mul; pw=F.pw
Wa=np.array(W); PW=np.array([[F.pw(x,e) for e in range(2*q)] for x in range(q)]); MUL=np.array(F.mul); ADD=np.array(F.add)
def esv(idx,k):
    E=[np.ones(N,dtype=np.int64)]+[np.zeros(N,dtype=np.int64) for _ in idx]
    for i in idx:
        for dd in range(len(idx),0,-1): E[dd]=ADD[E[dd],MUL[E[dd-1],Wa[:,i]]]
    return E[k] if 0<=k<=len(idx) else np.zeros(N,dtype=np.int64)
EP=[esv(P,k) for k in range(len(P)+1)]
target=MUL[PW[Wa[:,a],q-2],esv([i for i in range(n) if i!=b],f)]
print('|W|=%d  deg phi=%d'%(N,deg),flush=True)
S=Solver(F,N)
cols=sorted([(i+j+k,i,j,k) for i in range(q) for j in range(q) for k in range(len(P)+1) if i+j+k<=deg-1])
done=-1
for D,i,j,k in cols:
    if D!=done:
        ok,cb=S.solve(target)
        if ok: print('lift found using columns of degree <= %d'%done); break
        done=D
    S.add(MUL[MUL[PW[Wa[:,a],i],PW[Wa[:,b],j]],EP[k]],(i,j,k))
else:
    ok,cb=S.solve(target); print('all columns: ok=',ok)
print('rank',len(S.piv),' [%.1fs]'%(time.time()-T0))
