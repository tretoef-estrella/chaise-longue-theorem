# INFORME_7 STEP 1.3: structured ansatz for g := s0 + t_l on W_0 (k=2): g == sum c * y_j^a y_l^b e1(P)^c e2(P)^d, degree <= q-1 ?
import itertools, sys
from fq import Fq
q=int(sys.argv[1]); F=Fq(q); k=2; n=4; W=F.W0(k); j,l=1,0; P=[2,3]
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
s0=ev(lambda y: F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2)])
tl=ev(lambda y: F.mul[F.pw(y[j],q-1)][F.p(*[y[m] for m in P])])
g=[F.add[a][b] for a,b in zip(s0,tl)]
E=Elim(); items=[]
D=q-1
for tot in range(D+1):
    for a in range(tot+1):
        for b in range(tot+1-a):
            for d in range((tot-a-b)//2+1):
                c=tot-a-b-2*d
                f=lambda y,a=a,b=b,c=c,d=d: F.p(F.pw(y[j],a),F.pw(y[l],b),F.pw(F.esym([y[m] for m in P],1),c),F.pw(F.esym([y[m] for m in P],2),d))
                E.add(ev(f),{(a,b,c,d):1})
r,expr=E.reduce(g,{})
print("q=%d rank of ansatz %d ; g in ansatz span: %s"%(q,len(E.piv),all(x==0 for x in r)))
terms=[(m,F.neg[cf]) for m,cf in expr.items() if cf]
terms.sort(key=lambda t:(t[0][0]+t[0][1]+t[0][2]+2*t[0][3],t[0]))
print("g == " + " + ".join("%d*yj^%d yl^%d e1P^%d e2P^%d"%(cf,*m) for m,cf in terms))
