# INFORME_7 STEP 1.6: which building-block functions on W_0 have representatives of degree <= q+2k-5 (ansatz A1+A3 of desc3n)?
import itertools, sys, numpy as np
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
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
def parts(maxpart, D):
    out=[()]
    def rec(cur, last, rem):
        for p_ in range(last, maxpart+1):
            if p_<=rem: out.append(cur+(p_,)); rec(cur+(p_,), p_, rem-p_)
    rec((), 1, D); return out
def elam(y,lam):
    r=1
    for p_ in lam: r=F.mul[r][F.esym([y[m] for m in P],p_)]
    return r
E=Elim()
def addf(name,f): E.add(ev(f),{name:1})
D1=2*k-1
for lam in parts(len(P),D1):
    for a in range(D1-sum(lam)+1):
        for b in range(D1-sum(lam)-a+1):
            addf(("A1",a,b,lam), lambda y,a=a,b=b,lam=lam: F.p(F.pw(y[j],a),F.pw(y[l],b),elam(y,lam)))
def ind(val,a):
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return r    # J_a(val) = sum_{i<q-1} (val/a)^i = [val=0]-[val=a]
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]], "yj-yl":lambda y:F.add[y[j]][F.neg[y[l]]]}
D3=2*k-3
for ln,lf in lins.items():
    for a in [1,F.m1]:
        for lam in parts(len(P),D3):
            for aa in range(D3-sum(lam)+1):
                for bb in range(D3-sum(lam)-aa+1):
                    addf(("J",ln,a,aa,bb,lam), lambda y,lf=lf,a=a,aa=aa,bb=bb,lam=lam: F.p(ind(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam)))
print("k=%d q=%d rank(A1+A3)=%d"%(k,q,len(E.piv)))
# building blocks
def zeros(y): return [m for m in range(n) if y[m]==0]
def Ep(y): return F.esym([y[m] for m in P],2*k-3)
def eps(y,r): return F.esym(list(y),r)
def R(y,b):  # R_b = sum_{i>=1} y_b^{2i-2} e_{2k-2-2i}(y)
    return F.s(*[F.mul[F.pw(y[b],2*i-2)][eps(y,2*k-2-2*i)] for i in range(1,k)])
def Rjl(y): return F.s(*[F.mul[F.mul[F.pw(y[j],2*a)][F.pw(y[l],2*b)]][eps(y,2*k-6-2*a-2*b)] for a in range(k-2) for b in range(k-2-a)]) if k>=3 else 0
targets={
 "g=[Z={m} in P]prod_{P\\m}": lambda y: Ep(y) if (len(zeros(y))==1 and zeros(y)[0] in P) else 0,
 "[yj=0]E'": lambda y: Ep(y) if y[j]==0 else 0,
 "[Z={j}](1+yl)Rl": lambda y: F.mul[F.add[1][y[l]]][R(y,l)] if zeros(y)==[j] else 0,
 "h=[Z={j,l,m}]prod_{P\\m}": lambda y: Ep(y) if (len(zeros(y))==3 and j in zeros(y) and l in zeros(y)) else 0,
 "[Z={l}]yjRj": lambda y: F.mul[y[j]][R(y,j)] if zeros(y)==[l] else 0,
 "[Z={l}]Rj": lambda y: R(y,j) if zeros(y)==[l] else 0,
 "[Z={l}]Omega_j": lambda y: F.s(*[F.mul[eps(y,2*r)][F.pw(y[j],2*k-2-2*r)] for r in range(k)]) if zeros(y)==[l] else 0,
 "[|Z|=1]prod_{x'\\Z}=e_{2k-2}(y)": lambda y: eps(y,2*k-2),
 "[Z={l}]": lambda y: 1 if zeros(y)==[l] else 0,
 "[Z={l}]yj": lambda y: y[j] if zeros(y)==[l] else 0,
 "[Z={l}]yj^2": lambda y: F.mul[y[j]][y[j]] if zeros(y)==[l] else 0,
 "[Z={l}]e_{2k-4}(y)": lambda y: eps(y,2*k-4) if zeros(y)==[l] else 0,
 "[Z={l}]yj e_{2k-4}(y)": lambda y: F.mul[y[j]][eps(y,2*k-4)] if zeros(y)==[l] else 0,
 "[Z={l}](1+yj)Rj": lambda y: F.mul[F.add[1][y[j]]][R(y,j)] if zeros(y)==[l] else 0,
 "[Z in P,|Z|=3] yj yl Rjl": lambda y: F.mul[F.mul[y[j]][y[l]]][Rjl(y)] if (len(zeros(y))==3 and all(m in P for m in zeros(y))) else 0,
 "[Z={m} in P] yj yl Rjl": lambda y: F.mul[F.mul[y[j]][y[l]]][Rjl(y)] if (len(zeros(y))==1 and zeros(y)[0] in P) else 0,
}
for name,f in targets.items():
    r,expr=E.reduce(ev(f),{}); ok=not np.any(r)
    print("  %-40s in span: %s"%(name,ok))
    if ok and len(sys.argv)>3:
        for m,cf in sorted(expr.items(), key=lambda t:str(t[0])):
            if cf: print("        %d * %s"%(F.neg[cf],m))
