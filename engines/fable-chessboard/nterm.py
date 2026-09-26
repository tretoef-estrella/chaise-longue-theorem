# INFORME_7 STEP 1.11: representative of N := [yj=0] yl R_l + [yl=0] yj R_j + [yj=yl=-1] R'_j in a small named ansatz (+ tau's).
import sys, numpy as np
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
def R(y,b): return F.s(*[F.mul[F.pw(y[b],2*i-2)][eps(y,2*k-2-2*i)] for i in range(1,k)])
def Rp(y,b): return F.s(*[F.mul[F.pw(y[b],2*i-2)][F.mul[i%3][eps(y,2*k-2-2*i)]] for i in range(1,k)])
def SigP(y): return F.p(*[F.add[1][y[m]] for m in P])
def N(y):
    t=[]
    if y[j]==0: t.append(F.mul[y[l]][R(y,l)])
    if y[l]==0: t.append(F.mul[y[j]][R(y,j)])
    if y[j]==m1 and y[l]==m1: t.append(Rp(y,j))
    return F.s(*t)
ADD=np.array(F.add,dtype=np.int16); MUL=np.array(F.mul,dtype=np.int16); NEG=np.array(F.neg,dtype=np.int16); INV=np.array(F.inv,dtype=np.int16)
def ev(f): return np.array([f(y) for y in W],dtype=np.int16)
class Elim:
    def __init__(self): self.piv={}
    def reduce(self,vec,expr):
        vec=vec.copy(); expr=dict(expr)
        for c,(r,re) in self.piv.items():
            f=int(vec[c])
            if f:
                vec=ADD[vec, NEG[MUL[f, r]]]
                for m,cf in re.items(): expr[m]=F.add[expr.get(m,0)][F.neg[F.mul[f][cf]]]
        return vec,expr
    def add(self,vec,expr):
        vec,expr=self.reduce(vec,expr); nz=np.nonzero(vec)[0]
        if len(nz)==0: return False
        c=int(nz[0]); inv=int(INV[vec[c]]); self.piv[c]=(MUL[inv,vec],{m:F.mul[inv][cf] for m,cf in expr.items()}); return True
E=Elim()
def addf(name,f): E.add(ev(f),{name:1})
named={"1":(lambda y:1,0),"Rj":(lambda y:R(y,j),2*k-4),"Rl":(lambda y:R(y,l),2*k-4),"R'j":(lambda y:Rp(y,j),2*k-4),"R'l":(lambda y:Rp(y,l),2*k-4),
       "D":(D,2*k-4),"e{2k-4}(y)":(lambda y:eps(y,2*k-4),2*k-4),"e{2k-4}(P)":(lambda y:eP(y,2*k-4),2*k-4),"E'":(lambda y:eP(y,2*k-3),2*k-3),
       "e{2k-5}(P)":(lambda y:eP(y,2*k-5),2*k-5),"e{2k-6}(y)":(lambda y:eps(y,2*k-6),2*k-6)}
big={"u":(lambda y:eP(y,2*k-2),2*k-2),"SigP":(SigP,2*k-2),"e{2k-2}(y)":(lambda y:eps(y,2*k-2),2*k-2),
     "Om_j":(lambda y:F.s(*[F.mul[eps(y,2*r)][F.pw(y[j],2*k-2-2*r)] for r in range(k)]),2*k-2),
     "Om_l":(lambda y:F.s(*[F.mul[eps(y,2*r)][F.pw(y[l],2*k-2-2*r)] for r in range(k)]),2*k-2),
     "e{2k-2}(x'\\j)":(lambda y:F.esym([y[m] for m in range(n) if m!=j],2*k-2),2*k-2),
     "e{2k-2}(x'\\l)":(lambda y:F.esym([y[m] for m in range(n) if m!=l],2*k-2),2*k-2)}
# order: tau's, then simple polys, then J-terms, then full indicators
addf("tau_jl", lambda y: F.mul[F.pw(y[j],q-1)][eP(y,2*k-2)])
addf("tau_lj", lambda y: F.mul[F.pw(y[l],q-1)][eP(y,2*k-2)])
allp=dict(named); allp.update(big)
for nm,(nf,dg) in allp.items():
    for aa in range(4):
        for bb in range(4):
            if dg+aa+bb<=2*k-1: addf(("A",aa,bb,nm), lambda y,aa=aa,bb=bb,nf=nf: F.p(F.pw(y[j],aa),F.pw(y[l],bb),nf(y)))
def Jf(val,a):
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return r
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]], "yj-yl":lambda y:F.add[y[j]][F.neg[y[l]]]}
for a in [m1,1]:
    for ln,lf in lins.items():
        for nm,(nf,dg) in named.items():
            for aa in range(3):
                for bb in range(3):
                    if dg+aa+bb<=2*k-3: addf(("J",-1 if a==m1 else 1,ln,aa,bb,nm), lambda y,lf=lf,a=a,aa=aa,bb=bb,nf=nf: F.p(Jf(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),nf(y)))
for ln,lf in lins.items():
    for nm,(nf,dg) in named.items():
        for aa in range(3):
            for bb in range(3):
                if dg+aa+bb<=2*k-4: addf(("Ind0",ln,aa,bb,nm), lambda y,lf=lf,aa=aa,bb=bb,nf=nf: F.p(F.add[1][F.neg[F.pw(lf(y),q-1)]],F.pw(y[j],aa),F.pw(y[l],bb),nf(y)))
r,expr=E.reduce(ev(N),{}); ok=not np.any(r)
print("k=%d q=%d rank=%d  N in span: %s"%(k,q,len(E.piv),ok))
if ok:
    for m,cf in sorted(expr.items(), key=lambda t:str(t[0])):
        if cf: print("   %d * %s"%(F.neg[cf],m))
