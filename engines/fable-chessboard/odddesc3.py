# odd descent with Pi_{x'} multiples: ansatz = low (deg<=2k-2) + J-terms (deg<=2k-4) + I0 (deg<=2k-5) + all tau' + Pi_{x'} * (y_j^a y_l^b e_lam(P), a+b+|lam| = q-3)
import itertools, sys, numpy as np
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k-1; j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1])]
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
def addf(name,f): E.add(ev(f),{name:1})
D1=2*k-2; D3=2*k-4; D0=2*k-5
for lam in parts(len(P),D1):
    for a in range(D1-sum(lam)+1):
        for b in range(D1-sum(lam)-a+1):
            addf(("A",a,b,lam), lambda y,a=a,b=b,lam=lam: F.p(F.pw(y[j],a),F.pw(y[l],b),elam(y,lam)))
def Jf(val,a):
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return r
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]], "yj-yl":lambda y:F.add[y[j]][F.neg[y[l]]]}
for ln,lf in lins.items():
    for a in [1,F.m1]:
        for lam in parts(len(P),D3):
            for aa in range(D3-sum(lam)+1):
                for bb in range(D3-sum(lam)-aa+1):
                    addf(("J",ln,a,aa,bb,lam), lambda y,lf=lf,a=a,aa=aa,bb=bb,lam=lam: F.p(Jf(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam)))
    for lam in parts(len(P),D0):
        for aa in range(D0-sum(lam)+1):
            for bb in range(D0-sum(lam)-aa+1):
                addf(("I0",ln,aa,bb,lam), lambda y,lf=lf,aa=aa,bb=bb,lam=lam: F.p(F.add[1][F.neg[F.pw(lf(y),q-1)]],F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam)))
rlow=len(E.piv)
s0=ev(lambda y: F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2*k-3)])
Pi=lambda y: F.p(*[y[m] for m in range(n)])
# Pi_{x'} multiples of degree q+2k-4: Pi * (deg q-3)
for lam in parts(len(P),q-3):
    for aa in range(q-3-sum(lam)+1):
        bb=q-3-sum(lam)-aa
        addf(("Pi",aa,bb,lam), lambda y,aa=aa,bb=bb,lam=lam: F.p(Pi(y),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam)))
rpi=len(E.piv)
okpi=not np.any(E.reduce(s0,{})[0])
for b in range(n):
    for bp in range(n):
        if b!=bp: addf(("tau",b,bp), lambda y,b=b,bp=bp: F.mul[F.pw(y[b],q-1)][F.p(*[y[m] for m in range(n) if m not in (b,bp)])])
r,expr=E.reduce(s0,{}); ok=not np.any(r)
print("k=%d q=%d |W'_0|=%d ranks: low %d, +Pi %d, +tau %d ; s'0 in low+Pi: %s ; in low+Pi+tau: %s"%(k,q,len(W),rlow,rpi,len(E.piv),okpi,ok))
if ok:
    for m,cf in sorted(expr.items(), key=lambda t:str(t[0])):
        if cf and m[0] in ("tau","Pi"): print("   %d * %s"%(F.neg[cf],m))
