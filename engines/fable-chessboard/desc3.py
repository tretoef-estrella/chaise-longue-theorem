# INFORME_7 STEP 1.4: structured ansatz for the descent identity at level k:
#   g := s0 + t_l  on W_0,  s0 = y_j^(q-2) e_{2k-2}(x' \ y_l),  t_l = y_j^(q-1) prod_{P} y,  P = x' \ {j,l}
# ansatz: A1 = y_j^a y_l^b e_lambda(P) (deg <= 2k-1); A2 = tau_{bb'} = y_b^(q-1) prod_{x'\{b,b'}} y (all ordered pairs);
#         A3 = Ind * (y_j^a y_l^b e_lambda(P), deg <= 2k-3), Ind in { [y_b = a] (a=+-1, via -sum_{i<q-1}(y_b/a)^i), y_b^(q-1) } for b in {j,l},
#              and the same for the linear forms y_j+y_l, y_j-y_l.
import itertools, sys
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k; W=F.W0(k); j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
def ev(f): return [f(y) for y in W]
class Elim:
    def __init__(self): self.piv={}
    def reduce(self,vec,expr):
        vec=list(vec); expr=dict(expr)
        for c in range(len(vec)):
            if vec[c]!=0 and c in self.piv:
                r,re=self.piv[c]; f=vec[c]
                for jj in range(len(vec)):
                    if r[jj]: vec[jj]=F.add[vec[jj]][F.neg[F.mul[f][r[jj]]]]
                for m,cf in re.items(): expr[m]=F.add[expr.get(m,0)][F.neg[F.mul[f][cf]]]
        return vec,expr
    def add(self,vec,expr):
        vec,expr=self.reduce(vec,expr)
        for c in range(len(vec)):
            if vec[c]!=0:
                inv=F.inv[vec[c]]; vec=[F.mul[inv][x] for x in vec]; expr={m:F.mul[inv][cf] for m,cf in expr.items()}
                self.piv[c]=(vec,expr); return True
        return False
s0=ev(lambda y: F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2*k-2)])
tl=ev(lambda y: F.mul[F.pw(y[j],q-1)][F.p(*[y[m] for m in P])])
g=[F.add[a][b] for a,b in zip(s0,tl)]
# partitions lambda for e_lambda(P): multisets of parts in 1..|P|, weight <= D
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
E=Elim(); order=[]
def addf(name,f):
    if E.add(ev(f),{name:1}): order.append(name)
# A1
D1=2*k-1
for lam in parts(len(P),D1):
    for a in range(D1-sum(lam)+1):
        for b in range(D1-sum(lam)-a+1):
            addf(("A1",a,b,lam), lambda y,a=a,b=b,lam=lam: F.p(F.pw(y[j],a),F.pw(y[l],b),elam(y,lam)))
# A2
for b in range(n):
    for bp in range(n):
        if b!=bp:
            addf(("tau",b,bp), lambda y,b=b,bp=bp: F.mul[F.pw(y[b],q-1)][F.p(*[y[m] for m in range(n) if m not in (b,bp)])])
# A3
def ind(val,a):
    if a==0: return F.pw(val,q-1)
    r=0; x=1; ia=F.inv[a]
    for i in range(q-1): r=F.add[r][x]; x=F.mul[x][F.mul[val][ia]]
    return F.neg[r]
lins={"yj":lambda y:y[j], "yl":lambda y:y[l], "yj+yl":lambda y:F.add[y[j]][y[l]], "yj-yl":lambda y:F.add[y[j]][F.neg[y[l]]]}
D3=2*k-3
for ln,lf in lins.items():
    for a in [1,F.m1,0]:
        for lam in parts(len(P),D3):
            for aa in range(D3-sum(lam)+1):
                for bb in range(D3-sum(lam)-aa+1):
                    addf(("I",ln,a,aa,bb,lam), lambda y,lf=lf,a=a,aa=aa,bb=bb,lam=lam: F.p(ind(lf(y),a),F.pw(y[j],aa),F.pw(y[l],bb),elam(y,lam)))
r,expr=E.reduce(g,{})
print("k=%d q=%d |W_0|=%d rank(ansatz)=%d ; g = s0 + t_l in span: %s"%(k,q,len(W),len(E.piv),all(x==0 for x in r)))
if all(x==0 for x in r):
    for m,cf in expr.items():
        if cf: print("   %d * %s"%(F.neg[cf], m))
