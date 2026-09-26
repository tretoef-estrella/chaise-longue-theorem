# INFORME_7 STEP 1.7: residual of the candidate main term for  phi - h  on W_0, grouped by piece type.
import itertools, sys
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
m1=F.m1
def zeros(y): return tuple(m for m in range(n) if y[m]==0)
def eps(y,r): return F.esym(list(y),r) if r>=0 else 0
def Ep(y): return F.esym([y[m] for m in P],2*k-3)
def R(y,b): return F.s(*[F.mul[F.pw(y[b],2*i-2)][eps(y,2*k-2-2*i)] for i in range(1,k)])
def R2(y): return F.s(*[F.mul[F.mul[F.pw(y[j],2*a)][F.pw(y[l],2*b)]][eps(y,2*k-8-2*a-2*b)] for a in range(k) for b in range(k) if 2*k-8-2*a-2*b>=0])
def SigP(y): return F.p(*[F.add[1][y[m]] for m in P])
def target(y):   # phi - h
    Z=zeros(y)
    if Z==(l,): return F.add[R(y,j)][F.neg[SigP(y)]]
    if Z==(j,): return F.add[R(y,l)][F.neg[SigP(y)]]
    if len(Z)==3 and j in Z and l in Z: return F.neg[Ep(y)]
    return 0
def cand(y):
    return F.s(R(y,j),R(y,l),F.neg[eps(y,2*k-4)],F.neg[SigP(y)],F.p(y[j],y[j],y[l],y[l],R2(y)))
def ptype(y):
    Z=zeros(y); zs="Z="+("l" if l in Z else "")+("j" if j in Z else "")+"P"*len([m for m in Z if m in P])
    tags=[]
    if y[j]==m1: tags.append("yj=-1")
    if y[l]==m1: tags.append("yl=-1")
    if y[j]==1: tags.append("yj=1")
    if y[l]==1: tags.append("yl=1")
    if y[j]!=0 and F.add[y[j]][y[l]]==0: tags.append("yl=-yj")
    if y[j]!=0 and y[j]==y[l]: tags.append("yl=yj")
    return zs+" "+",".join(tags)
from collections import defaultdict
stat=defaultdict(lambda:[0,0])
for y in W:
    r=F.add[target(y)][F.neg[cand(y)]]
    t=ptype(y); stat[t][0]+=1
    if r: stat[t][1]+=1
print("k=%d q=%d: piece type : #points, #nonzero residual"%(k,q))
for t in sorted(stat): print("   %-30s %6d %6d"%(t,*stat[t]))
