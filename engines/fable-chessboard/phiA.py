# lift of phi_ab on W_(1,1)(n), q=9: phi + sum c * u^i b^j e_k(P) [* anchor-free coefficients] == 0 on W ?
import sys, numpy as np, itertools, time
from fq import Fq
from ansatz12 import Solver
q=int(sys.argv[2]); n=int(sys.argv[1]); F=Fq(q); T0=time.time()
s1,s2=1,3
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[s1,s2])]
N=len(W); print('|W|=',N,flush=True)
a,b=0,1; P=list(range(2,n)); f=n-2; deg=q+f-2
def vec(fn): return np.array([fn(y) for y in W],dtype=np.int64)
ml=F.mul; pw=F.pw
target=vec(lambda y: ml[pw(y[a],q-2)][F.esym([y[i] for i in range(n) if i!=b],f)])
S=Solver(F,N)
extra=sys.argv[3] if len(sys.argv)>3 else ''
cols=[]
for i in range(q):
    for j in range(q):
        for k in range(len(P)+1):
            if i+j+k<=deg-1: cols.append(('u^%d b^%d e%d(P)'%(i,j,k),(lambda i,j,k: lambda y: ml[ml[pw(y[a],i)][pw(y[b],j)]][F.esym([y[t] for t in P],k)])(i,j,k)))
if 'p' in extra:   # add power sums p_m(P), m odd, times u^i b^j e_k(P), degree-bounded
    for m in range(1,q-1,2):
        for i in range(q):
            for j in range(q):
                for k in range(len(P)+1):
                    if i+j+k+m<=deg-1:
                        cols.append(('u^%d b^%d e%d(P) p%d(P)'%(i,j,k,m),(lambda i,j,k,m: lambda y: ml[ml[ml[pw(y[a],i)][pw(y[b],j)]][F.esym([y[t] for t in P],k)]][F.s(*[pw(y[t],m) for t in P])])(i,j,k,m)))
print('columns',len(cols),flush=True)
for name,fn in cols: S.add(vec(fn),name)
ok,cb=S.solve(target)
print('phi_ab in span (lift exists in ansatz):',ok,' rank',len(S.piv),' [%.1fs]'%(time.time()-T0))
if ok:
    for k,x in sorted(cb.items()): print('   ',x,k)
