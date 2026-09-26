# odd descent, FULL monomial space: is s'0 in F_{q+2k-6}(W'_0) + span(tau'_{bb'}) + span(Pi_{x'} * monomials of degree q-3)? (k=2,3 ; q=9)
import itertools, sys, numpy as np
from fq import Fq
k=int(sys.argv[1]); q=int(sys.argv[2]); F=Fq(q); n=2*k-1; j,l=1,0; P=[m for m in range(n) if m not in (j,l)]
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1])]
ADD=np.array(F.add,dtype=np.int16); MUL=np.array(F.mul,dtype=np.int16); NEG=np.array(F.neg,dtype=np.int16); INV=np.array(F.inv,dtype=np.int16)
Wa=np.array(W,dtype=np.int16)
Dmax=q+2*k-6; PW=np.zeros((q,Dmax+1),dtype=np.int16)
for a in range(q):
    for e_ in range(Dmax+1): PW[a][e_]=F.pw(a,e_)
def mono(e):
    v=np.ones(len(W),dtype=np.int16)
    for i in range(n):
        if e[i]: v=MUL[v,PW[Wa[:,i],e[i]]]
    return v
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
E=Elim(); Dmax=q+2*k-6
for tot in range(Dmax+1):
    for e in itertools.product(range(tot+1),repeat=n):
        if sum(e)==tot: E.add(mono(e))
rF=len(E.piv)
s0=np.array([F.mul[F.pw(y[j],q-2)][F.esym([y[m] for m in range(n) if m!=l],2*k-3)] for y in W],dtype=np.int16)
tl=np.array([F.mul[F.pw(y[j],q-1)][F.p(*[y[m] for m in P])] for y in W],dtype=np.int16)
inF=not np.any(E.reduce(ADD[s0,tl]))
inF0=not np.any(E.reduce(s0))
for b in range(n):
    for bp in range(n):
        if b!=bp: E.add(np.array([F.mul[F.pw(y[b],q-1)][F.p(*[y[m] for m in range(n) if m not in (b,bp)])] for y in W],dtype=np.int16))
rT=len(E.piv); inT=not np.any(E.reduce(s0))
Pi=np.array([F.p(*y) for y in W],dtype=np.int16)
for e in itertools.product(range(q-2),repeat=n):
    if sum(e)==q-3: E.add(MUL[Pi,mono(e)])
rP=len(E.piv); inP=not np.any(E.reduce(s0))
print("k=%d q=%d |W'_0|=%d dim F_{q+2k-6}=%d ; s'0+tau' in F: %s ; s'0 in F: %s ; +tau's rank %d, s'0 in: %s ; +Pi*deg(q-3) rank %d, s'0 in: %s"%(k,q,len(W),rF,inF,inF0,rT,inT,rP,inP))
