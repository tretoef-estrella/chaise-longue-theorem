# INFORME_7 STEP 1.10: (a) test the full hand-derived identity (true indicators); (b) test low-degree membership of the nuisance pieces.
import sys, numpy as np
from collections import defaultdict
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
m1=F.m1
def zeros(y): return tuple(m for m in range(n) if y[m]==0)
def eps(y,r): return F.esym(list(y),r) if r>=0 else 0
def eP(y,r): return F.esym([y[m] for m in P],r) if r>=0 else 0
def hcomp(a,b,d): return F.s(*[F.mul[F.pw(a,i)][F.pw(b,d-i)] for i in range(d+1)]) if d>=0 else 0
def D(y):
    a=F.mul[y[j]][y[j]]; b=F.mul[y[l]][y[l]]
    return F.s(*[F.mul[eps(y,2*k-2-2*i)][hcomp(a,b,i-1)] for i in range(1,k)])
def Rp(y,bidx): return F.s(*[F.mul[F.pw(y[bidx],2*i-2)][F.mul[i%3][eps(y,2*k-2-2*i)]] for i in range(1,k)])
def SigP(y): return F.p(*[F.add[1][y[m]] for m in P])
def g(y):
    Z=zeros(y); return eP(y,2*k-3) if (len(Z)==1 and Z[0] in P) else 0
def formula(y):
    yj,yl=y[j],y[l]
    t=[eP(y,2*k-3), eP(y,2*k-2), D(y), F.neg[SigP(y)]]
    if F.add[yj][yl]==0: t.append(F.neg[Rp(y,j)])
    if yj==yl: t.append(F.mul[F.add[1][F.neg[yj]]][Rp(y,j)])
    if yj==m1: t.append(F.neg[F.mul[yl][D(y)]])
    if yl==m1: t.append(F.neg[F.mul[yj][D(y)]])
    if yj==1: t.append(F.neg[F.mul[yl][D(y)]])
    if yl==1: t.append(F.neg[F.mul[yj][D(y)]])
    return F.s(*t)
bad=sum(1 for y in W if g(y)!=formula(y))
print("k=%d q=%d |W_0|=%d  full identity (true indicators) fails at %d points"%(k,q,len(W),bad))
# (b) membership tests in span(A1+A3)
ADD=np.array(F.add,dtype=np.int16); MUL=np.array(F.mul,dtype=np.int16); NEG=np.array(F.neg,dtype=np.int16); INV=np.array(F.inv,dtype=np.int16)
def ev(f): return np.array([f(y) for y in W],dtype=np.int16)
class Elim:
    def __init__(self): self.piv={}
    def reduce(self,vec):
        vec=vec.copy()
        for c,r in self.piv.items():
            f=int(vec[c])
            if f: vec=ADD[vec, NEG[MUL[f, r]]]
        return vec
    def add(self,vec):
        vec=self.reduce(vec); nz=np.nonzero(vec)[0]
        if len(nz)==0: return False
        c=int(nz[0]); self.piv[c]=MUL[int(INV[vec[c]]),vec]; return True
def parts(maxpart, Dg):
    out=[()]
    def rec(cur, last, rem):
        for p_ in range(last, maxpart+1):
            if p_<=rem: out.append(cur+(p_,)); rec(cur+(p_,), p_, rem-p_)
    rec((), 1, Dg); return out
def elam(y,lam):
    r=1
    for p_ in lam: r=F.mul[r][F.esym([y[m] for m in P],p_)]
    return r
E=Elim()
for lam in parts(len(P),2*k-1):
    for a in range(2*k-1-sum(lam)+1):
        for b in range(2*k-1-sum(lam)-a+1):
            E.add(ev(lambda y,a=a,b=b,lam=lam: F.p(F.pw(y[j],a),F.pw(y[l],b),elam(y,lam))))
def Jf(val,a):
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return r
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]], "yj-yl":lambda y:F.add[y[j]][F.neg[y[l]]]}
for ln,lf in lins.items():
    for a in [1,m1]:
        for lam in parts(len(P),2*k-3):
            for aa in range(2*k-3-sum(lam)+1):
                for bb in range(2*k-3-sum(lam)-aa+1):
                    E.add(ev(lambda y,lf=lf,a=a,aa=aa,bb=bb,lam=lam: F.p(Jf(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam))))
# also full indicators 1-x^{q-1} times degree <= 2k-4
for ln,lf in lins.items():
    for lam in parts(len(P),2*k-4):
        for aa in range(2*k-4-sum(lam)+1):
            for bb in range(2*k-4-sum(lam)-aa+1):
                E.add(ev(lambda y,lf=lf,aa=aa,bb=bb,lam=lam: F.p(F.add[1][F.neg[F.pw(lf(y),q-1)]],F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam))))
print("   rank of ansatz (A1 + J-terms + full-indicator terms):",len(E.piv))
tests={
 "g": g,
 "[yj=yl=-1] R'_j": lambda y: Rp(y,j) if (y[j]==m1 and y[l]==m1) else 0,
 "[yj=yl] yj R'_j": lambda y: F.mul[y[j]][Rp(y,j)] if y[j]==y[l] else 0,
 "[yj=yl] R'_j": lambda y: Rp(y,j) if y[j]==y[l] else 0,
 "[yj+yl=0] R'_j": lambda y: Rp(y,j) if F.add[y[j]][y[l]]==0 else 0,
 "[yj=-1] yl D": lambda y: F.mul[y[l]][D(y)] if y[j]==m1 else 0,
 "[yj=1] yl D": lambda y: F.mul[y[l]][D(y)] if y[j]==1 else 0,
 "[yj=-1] yl D + [yl=-1] yj D": lambda y: F.add[F.mul[y[l]][D(y)] if y[j]==m1 else 0][F.mul[y[j]][D(y)] if y[l]==m1 else 0],
 "[yj=-1](yl D) - [yj=0](yl D)  (= -J_{-1}(yj) yl D)": lambda y: F.add[F.mul[y[l]][D(y)] if y[j]==m1 else 0][F.neg[F.mul[y[l]][D(y)]] if y[j]==0 else 0],
 "[yj=1] yl D - [yj=0] yl D": lambda y: F.add[F.mul[y[l]][D(y)] if y[j]==1 else 0][F.neg[F.mul[y[l]][D(y)]] if y[j]==0 else 0],
 "[yj=0] yl D": lambda y: F.mul[y[l]][D(y)] if y[j]==0 else 0,
 "[yj+yl=1] R'_j": lambda y: Rp(y,j) if F.add[y[j]][y[l]]==1 else 0,
 "[yj-yl=1] yj R'_j": lambda y: F.mul[y[j]][Rp(y,j)] if F.add[y[j]][F.neg[y[l]]]==1 else 0,
}
for nm,f in tests.items():
    r=E.reduce(ev(f)); print("   %-55s in low-degree span: %s"%(nm, not np.any(r)))
