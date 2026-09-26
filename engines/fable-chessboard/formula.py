# INFORME_7 STEP 1.9: test the hand-derived identity for g on W_0 with TRUE indicators, residual by piece type.
import sys
from collections import defaultdict
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
m1=F.m1
def zeros(y): return tuple(m for m in range(n) if y[m]==0)
def eps(y,r): return F.esym(list(y),r) if r>=0 else 0
def eP(y,r): return F.esym([y[m] for m in P],r) if r>=0 else 0
def hcomp(a,b,d):  # complete homogeneous h_d(a,b)
    return F.s(*[F.mul[F.pw(a,i)][F.pw(b,d-i)] for i in range(d+1)]) if d>=0 else 0
def D(y):   # D_{jl} = ev[yj^2, yl^2] = sum_{i>=1} eps_{2k-2-2i} h_{i-1}(yj^2, yl^2)
    a=F.mul[y[j]][y[j]]; b=F.mul[y[l]][y[l]]
    return F.s(*[F.mul[eps(y,2*k-2-2*i)][hcomp(a,b,i-1)] for i in range(1,k)])
def Rp(y,bidx):  # R'_b = sum_{i>=1} i eps_{2k-2-2i} y_b^{2i-2}
    return F.s(*[F.mul[F.pw(y[bidx],2*i-2)][F.mul[i%3][eps(y,2*k-2-2*i)]] for i in range(1,k)])
def SigP(y): return F.p(*[F.add[1][y[m]] for m in P])
def g(y):
    Z=zeros(y)
    return eP(y,2*k-3) if (len(Z)==1 and Z[0] in P) else 0
def I(c): return 1 if c else 0
def formula(y):
    yj,yl=y[j],y[l]
    t=[eP(y,2*k-3), eP(y,2*k-2), D(y), F.neg[SigP(y)]]
    if F.add[yj][yl]==0: t.append(F.neg[Rp(y,j)])
    if yj==yl: t.append(F.neg[Rp(y,j)])
    if yj==m1: t.append(F.neg[F.mul[yl][D(y)]])
    if yl==m1: t.append(F.neg[F.mul[yj][D(y)]])
    return F.s(*t)
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
stat=defaultdict(lambda:[0,0,set()])
for y in W:
    r=F.add[g(y)][F.neg[formula(y)]]
    t=ptype(y); stat[t][0]+=1
    if r:
        stat[t][1]+=1
        # compare residual with R'(1)-type values
        stat[t][2].add(("r=R'_j" if r==Rp(y,j) else "r=-R'_j" if r==F.neg[Rp(y,j)] else "r=e{2k-4}" if r==eps(y,2*k-4) else "r=-e{2k-4}" if r==F.neg[eps(y,2*k-4)] else "other"))
print("k=%d q=%d"%(k,q))
for t in sorted(stat):
    if stat[t][1]: print("   %-30s %6d nonzero of %6d   %s"%(t,stat[t][1],stat[t][0],sorted(stat[t][2])))
print("   total nonzero:",sum(v[1] for v in stat.values()))
