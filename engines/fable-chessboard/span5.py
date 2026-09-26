# INFORME_9 STEP 2: on W = W_(1)(n) (n odd, m = 1): is a function phi in  F_{d-2}(W) + known_{d-1} + (N_0 + e_n)_d  (all as functions on W)?
import itertools, sys, numpy as np
from fq import Fq
n=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); d=q+n-3; j,l=0,1; P=[i for i in range(n) if i not in (j,l)]
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1])]
Wa=np.array(W,dtype=np.int16); N=len(W)
ADD=np.array(F.add,dtype=np.int16); MUL=np.array(F.mul,dtype=np.int16); NEG=np.array(F.neg,dtype=np.int16); INV=np.array(F.inv,dtype=np.int16)
PW=np.zeros((q,2*q+n),dtype=np.int16)
for a in range(q):
    for e in range(2*q+n): PW[a][e]=F.pw(a,e)
def mono(e):
    v=np.ones(N,dtype=np.int16)
    for i in range(n):
        if e[i]: v=MUL[v,PW[Wa[:,i],e[i]]]
    return v
def esymv(idx,k):
    E=[np.ones(N,dtype=np.int16)]+[np.zeros(N,dtype=np.int16) for _ in range(len(idx))]
    for i in idx:
        xi=Wa[:,i]
        for dd in range(len(idx),0,-1): E[dd]=ADD[E[dd],MUL[E[dd-1],xi]]
    return E[k] if 0<=k<=len(idx) else np.zeros(N,dtype=np.int16)
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
def monos(deg):
    return [e for e in itertools.product(range(deg+1),repeat=n) if sum(e)==deg]
def build(extra_tau):
    E=Elim()
    for t in range(d-1):          # F_{d-2}
        for e in monos(t): E.add(mono(e))
    r0=len(E.piv)
    # known_{d-1}: e_j (j odd or j = n-1) * monomials of degree d-1-j ; box: x_i^q * deg (d-1-q)
    for jj in [k for k in range(1,n+1) if k%2==1 or k==n-1]:
        ej=esymv(list(range(n)),jj)
        for e in monos(d-1-jj): E.add(MUL[ej,mono(e)])
    for i in range(n):
        if d-1-q>=0:
            for e in monos(d-1-q): E.add(MUL[PW[Wa[:,i],q],mono(e)])
    r1=len(E.piv)
    for v in extra_tau: E.add(v)
    return E,r0,r1
def taus(kind):
    out=[]
    if kind in ("jl","all"):
        for C in itertools.combinations(P,n-2): out.append(MUL[PW[Wa[:,j],q-1],mono([1 if i in C else 0 for i in range(n)])])
    if kind=="all":
        for a in range(n):
            for C in itertools.combinations([i for i in range(n) if i!=a],n-2): out.append(MUL[PW[Wa[:,a],q-1],mono([1 if i in C else 0 for i in range(n)])])
        en=esymv(list(range(n)),n)
        for e in monos(q-3): out.append(MUL[en,mono(e)])
    return out
u=Wa[:,j]; yl=Wa[:,l]; PiP=mono([1 if i in P else 0 for i in range(n)]); en3=esymv(P,n-3)
s_jl=MUL[PW[u,q-2],esymv([i for i in range(n) if i!=l],n-2)]; tau_jl=MUL[PW[u,q-1],PiP]
s_lj=MUL[PW[yl,q-2],esymv([i for i in range(n) if i!=j],n-2)]
targets={"s_jl+tau_jl":ADD[s_jl,tau_jl], "s_jl":s_jl, "u^(q-1)y_l^(q-1)e_{n-3}(P)":MUL[MUL[PW[u,q-1],PW[yl,q-1]],en3],
 "y_l^(q-2)Pi_P":MUL[PW[yl,q-2],PiP], "u^(q-1)y_l^(q-2)Pi_P":MUL[PW[u,q-1],MUL[PW[yl,q-2],PiP]], "u^(q-1)e_{n-3}(P)":MUL[PW[u,q-1],en3],
 "y_l^(q-1)e_{n-3}(P)":MUL[PW[yl,q-1],en3], "s_lj":s_lj, "y_l^(q-2)Pi_P+u^(q-1)e_{n-3}(P)":ADD[MUL[PW[yl,q-2],PiP],MUL[PW[u,q-1],en3]],
 "(O') rhs: -y_l^(q-2)Pi_P-u^(q-1)e_{n-3}(P)+u^(q-1)y_l^(q-1)e_{n-3}(P)":ADD[ADD[NEG[MUL[PW[yl,q-2],PiP]],NEG[MUL[PW[u,q-1],en3]]],MUL[MUL[PW[u,q-1],PW[yl,q-1]],en3]]}
for kind in ("none","jl","all"):
    E,r0,r1=build(taus(kind))
    print("n=%d q=%d |W|=%d d=%d  tau-kind=%s : dims F_{d-2}=%d, +known=%d, +tau=%d"%(n,q,N,d,kind,r0,r1,len(E.piv)),flush=True)
    for name,v in targets.items(): print("   %-70s in span? %s"%(name, not np.any(E.reduce(v))),flush=True)
