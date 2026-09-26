# INFORME_7 STEP 2 (B): odd descent test on W'_0 = V_1^{(k-1)} = {y in F_q^{2k-1} : y u {1} closed}:
#   s'0 = y_j^(q-2) e_{2k-3}(x'\y_l), tau' = y_j^(q-1) prod_{P} y (P = x'\{j,l}, |P| = 2k-3); is g' := s'0 + tau' of degree <= q+2k-6 ?
import itertools, sys, numpy as np
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k-1; j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1])]
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
E=Elim(); D1=2*k-2; D3=2*k-4   # r degree <= q+2k-6 = (q-2)+(2k-4)
for lam in parts(len(P),D1):
    for a in range(D1-sum(lam)+1):
        for b in range(D1-sum(lam)-a+1):
            E.add(ev(lambda y,a=a,b=b,lam=lam: F.p(F.pw(y[j],a),F.pw(y[l],b),elam(y,lam))))
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
                    E.add(ev(lambda y,lf=lf,a=a,aa=aa,bb=bb,lam=lam: F.p(Jf(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam))))
rankA=len(E.piv)
s0=ev(lambda y: F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2*k-3)])
tl=ev(lambda y: F.mul[F.pw(y[j],q-1)][F.p(*[y[m] for m in P])])
g=ADD[s0,tl]
print("k=%d q=%d |W'_0|=%d rank(ansatz)=%d ; g'=s'0+tau' in low span: %s ; s'0 alone: %s ; tau' alone: %s"%(k,q,len(W),rankA,not np.any(E.reduce(g)),not np.any(E.reduce(s0)),not np.any(E.reduce(tl))))
# other (3,9) interaction elements: y_l^3 y_j^(q-2) (l=0? the log had y_3^3 y_4^(q-2)); test y_b^3 y_j^(q-2) for b in P, and y_j^(q-2) e_3(4 vars)
for b in P[:1]:
    m=ev(lambda y,b=b: F.mul[F.pw(y[b],3)][F.pw(y[j],q-2)])
    print("   y_%d^3 y_j^(q-2) + tau': %s ; alone: %s"%(b, not np.any(E.reduce(ADD[m,tl])), not np.any(E.reduce(m))))
