# INFORME_7 STEP 1.8: express the residual rho := (phi - h) - cand  (supported on coincidence pieces) in a NAMED k-general ansatz.
import itertools, sys, numpy as np
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
m1=F.m1
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
        vec,expr=self.reduce(vec,expr)
        nz=np.nonzero(vec)[0]
        if len(nz)==0: return False
        c=int(nz[0]); inv=int(INV[vec[c]]); vec=MUL[inv,vec]; expr={m:F.mul[inv][cf] for m,cf in expr.items()}
        self.piv[c]=(vec,expr); return True
def zeros(y): return tuple(m for m in range(n) if y[m]==0)
def eps(y,r): return F.esym(list(y),r) if r>=0 else 0
def eP(y,r): return F.esym([y[m] for m in P],r) if r>=0 else 0
def R(y,b): return F.s(*[F.mul[F.pw(y[b],2*i-2)][eps(y,2*k-2-2*i)] for i in range(1,k)])
def Rjl(y): return F.s(*[F.mul[F.mul[F.pw(y[j],2*a)][F.pw(y[l],2*b)]][eps(y,2*k-6-2*a-2*b)] for a in range(k) for b in range(k) if 2*k-6-2*a-2*b>=0])
def R2(y): return F.s(*[F.mul[F.mul[F.pw(y[j],2*a)][F.pw(y[l],2*b)]][eps(y,2*k-8-2*a-2*b)] for a in range(k) for b in range(k) if 2*k-8-2*a-2*b>=0])
def SigP(y): return F.p(*[F.add[1][y[m]] for m in P])
def Om(y,b): return F.s(*[F.mul[eps(y,2*r)][F.pw(y[b],2*k-2-2*r)] for r in range(k)])
def target(y):
    Z=zeros(y)
    if Z==(l,): return F.add[R(y,j)][F.neg[SigP(y)]]
    if Z==(j,): return F.add[R(y,l)][F.neg[SigP(y)]]
    if len(Z)==3 and j in Z and l in Z: return F.neg[eP(y,2*k-3)]
    return 0
def cand(y): return F.s(R(y,j),R(y,l),F.neg[eps(y,2*k-4)],F.neg[SigP(y)],F.p(y[j],y[j],y[l],y[l],R2(y)))
rho=ev(lambda y: F.add[target(y)][F.neg[cand(y)]])
named={"1":lambda y:1, "Rj":lambda y:R(y,j), "Rl":lambda y:R(y,l), "Rjl":Rjl, "R2":R2,
       "e{2k-4}(y)":lambda y:eps(y,2*k-4), "e{2k-6}(y)":lambda y:eps(y,2*k-6),
       "e{2k-4}(P)":lambda y:eP(y,2*k-4), "E'=e{2k-3}(P)":lambda y:eP(y,2*k-3), "e{2k-5}(P)":lambda y:eP(y,2*k-5), "e{2k-6}(P)":lambda y:eP(y,2*k-6)}
deg={"1":0,"Rj":2*k-4,"Rl":2*k-4,"Rjl":2*k-6,"R2":2*k-8,"e{2k-4}(y)":2*k-4,"e{2k-6}(y)":2*k-6,"e{2k-4}(P)":2*k-4,"E'=e{2k-3}(P)":2*k-3,"e{2k-5}(P)":2*k-5,"e{2k-6}(P)":2*k-6}
def Jf(val,a):
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return r
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]]}
E=Elim()
def addf(name,f): E.add(ev(f),{name:1})
# J-terms first (the expected corrections), ordered: J_{-1}(yj), J_{-1}(yl), J_{-1}(yj+yl), then J_1(...)
for a in [m1,1]:
    for ln,lf in lins.items():
        for nm,nf in named.items():
            if deg[nm]<0: continue
            for aa in range(3):
                for bb in range(3):
                    if deg[nm]+aa+bb<=2*k-3:
                        addf(("J",a if a==1 else -1,ln,aa,bb,nm), lambda y,lf=lf,a=a,aa=aa,bb=bb,nf=nf: F.p(Jf(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),nf(y)))
# then polynomial terms of degree <= 2k-1
named2=dict(named); named2.update({"SigP":SigP,"Om_j":lambda y:Om(y,j),"Om_l":lambda y:Om(y,l),"e{2k-2}(y)":lambda y:eps(y,2*k-2),"u=e{2k-2}(P)":lambda y:eP(y,2*k-2)})
deg2=dict(deg); deg2.update({"SigP":2*k-2,"Om_j":2*k-2,"Om_l":2*k-2,"e{2k-2}(y)":2*k-2,"u=e{2k-2}(P)":2*k-2})
for nm,nf in named2.items():
    for aa in range(4):
        for bb in range(4):
            if deg2[nm]>=0 and deg2[nm]+aa+bb<=2*k-1:
                addf(("A",aa,bb,nm), lambda y,aa=aa,bb=bb,nf=nf: F.p(F.pw(y[j],aa),F.pw(y[l],bb),nf(y)))
r,expr=E.reduce(rho,{}); ok=not np.any(r)
print("k=%d q=%d rank=%d rho in span: %s"%(k,q,len(E.piv),ok))
if ok:
    for m,cf in sorted(expr.items(), key=lambda t:str(t[0])):
        if cf: print("   %d * %s"%(F.neg[cf],m))
