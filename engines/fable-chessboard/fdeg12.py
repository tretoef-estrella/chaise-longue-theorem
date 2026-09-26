# fdeg12.py — Fable 12: function degree on W_mu(n) (q = 9) by exact GF(q) elimination of monomial functions, degree by degree.
# fdeg(g) = least d such that g|W is a combination of monomials of degree <= d.  g in gr I(W)  <=>  fdeg(g) < deg g.
import itertools, sys, numpy as np
from fq import Fq
class Space:
    def __init__(self, q, W):
        F=Fq(q); self.F=F; self.q=q
        self.Wa=np.array(W,dtype=np.int64); self.N=len(W); self.n=self.Wa.shape[1]
        self.ADD=np.array(F.add); self.MUL=np.array(F.mul); self.NEG=np.array(F.neg); self.INV=np.array(F.inv)
        self.PW=np.array([[F.pw(a,e) for e in range(3*q)] for a in range(q)])
        self.piv={}   # col -> normalized row (fully reduced not required)
        self.deg=-1
    def mono(self,e):
        v=np.ones(self.N,dtype=np.int64)
        for i,k in enumerate(e):
            if k: v=self.MUL[v,self.PW[self.Wa[:,i],k]]
        return v
    def reduce(self,v):
        v=v.copy()
        for c,r in self.piv.items():
            f=v[c]
            if f: v=self.ADD[v,self.NEG[self.MUL[f,r]]]
        return v
    def add(self,v):
        v=self.reduce(v); nz=np.nonzero(v)[0]
        if len(nz)==0: return False
        c=int(nz[0]); self.piv[c]=self.MUL[self.INV[v[c]],v]; return True
    def upto(self,d):
        while self.deg<d and len(self.piv)<self.N:
            self.deg+=1; D=self.deg
            for e in itertools.product(range(min(D,self.q-1)+1),repeat=self.n):
                if sum(e)==D: self.add(self.mono(e))
        self.deg=max(self.deg,d)
    def inspan(self,v): return not np.any(self.reduce(v))
    def fdeg(self,v,dmax):
        for d in range(0,dmax+1):
            self.upto(d)
            if self.inspan(v): return d
        return None
def fibre(q,n,anch):
    F=Fq(q)
    return [y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+anch)]
