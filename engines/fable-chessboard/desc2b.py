# INFORME_7 STEP 1.2: at k=2, q=9: find alpha and a representative r (in a greedy standard-monomial basis of F_{q-1}(W_0)) with
#   s0 - alpha*t_l == r on W_0,  s0 = x_j^(q-2) e_2(V), V = x'\x_l, t_l = x_j^(q-1) x_{x'\{j,l}},  j=1, l=0.
import itertools
from fq import Fq
q=9; F=Fq(q); k=2; n=4; W=F.W0(k)
def ev(f): return [f(y) for y in W]
def monos(n,d):
    out=[]
    for tot in range(d+1):
        for e in itertools.product(range(tot+1),repeat=n):
            if sum(e)==tot: out.append(e)
    return out
def mono(e): return lambda y: F.p(*[F.pw(y[i],e[i]) for i in range(n)])
class Elim:
    def __init__(self): self.piv={}; self.rowexpr={}
    def reduce(self,vec,expr):
        vec=list(vec); expr=dict(expr)
        for c in range(len(vec)):
            if vec[c]!=0 and c in self.piv:
                r,re=self.piv[c]; f=vec[c]
                for j in range(len(vec)):
                    if r[j]: vec[j]=F.add[vec[j]][F.neg[F.mul[f][r[j]]]]
                for m,cf in re.items(): expr[m]=F.add[expr.get(m,0)][F.neg[F.mul[f][cf]]]
        return vec,expr
    def add(self,vec,expr):
        vec,expr=self.reduce(vec,expr)
        for c in range(len(vec)):
            if vec[c]!=0:
                inv=F.inv[vec[c]]; vec=[F.mul[inv][x] for x in vec]; expr={m:F.mul[inv][cf] for m,cf in expr.items()}
                self.piv[c]=(vec,expr); return True
        return False
E=Elim(); basis=[]
for e in monos(n,q-1):
    if E.add(ev(mono(e)),{e:1}): basis.append(e)
print("dim F_{q-1}(W_0) =",len(basis))
j,l=1,0; C=[2,3]
s0=ev(lambda y: F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2)])
tl=ev(lambda y: F.mul[F.pw(y[j],q-1)][F.p(*[y[m] for m in C])])
tls=ev(lambda y: F.mul[F.pw(y[l],q-1)][F.p(*[y[m] for m in C])])
def show(expr):
    names=["x0","x1","x2","x3"]
    terms=[]
    for m,cf in sorted(expr.items(), key=lambda t:(sum(t[0]),t[0])):
        if cf: terms.append("%s*%s"%(cf,"".join("%s^%d"%(names[i],m[i]) if m[i]>1 else names[i] for i in range(n) if m[i])))
    return " + ".join(terms) if terms else "0"
for alpha in range(q):
    v=[F.add[s0[i]][F.neg[F.mul[alpha][tl[i]]]] for i in range(len(W))]
    r,expr=E.reduce(v,{})
    if all(x==0 for x in r):
        print("alpha =",alpha,"(field element code; 1=one, 2=-1):  s0 - alpha*t_l ==", show({m:F.neg[c] for m,c in expr.items()}))
for alpha in range(q):
    v=[F.add[s0[i]][F.neg[F.mul[alpha][tls[i]]]] for i in range(len(W))]
    r,expr=E.reduce(v,{})
    if all(x==0 for x in r):
        print("alpha =",alpha,":  s0 - alpha*t_l^swap ==", show({m:F.neg[c] for m,c in expr.items()}))
