# ansatz12.py — Fable 12: is target = sum_i c_i g_i on W (exact GF(q))?  returns the coefficients (tracked elimination).
import numpy as np, itertools
from fq import Fq
class Solver:
    def __init__(self,F,N):
        self.F=F; self.N=N
        self.ADD=np.array(F.add); self.MUL=np.array(F.mul); self.NEG=np.array(F.neg); self.INV=np.array(F.inv)
        self.piv=[]   # (col, row vector, combo dict)
    def reduce(self,v,combo):
        v=v.copy(); combo=dict(combo)
        for c,r,cb in self.piv:
            f=int(v[c])
            if f:
                nf=int(self.NEG[f]); v=self.ADD[v,self.MUL[nf,r]]
                for k,x in cb.items(): combo[k]=int(self.F.add[combo.get(k,0)][self.F.mul[nf][x]])
        return v,{k:x for k,x in combo.items() if x}
    def add(self,v,name):
        v,cb=self.reduce(v,{name:1}); nz=np.nonzero(v)[0]
        if len(nz)==0: return cb   # a relation among the g's
        c=int(nz[0]); iv=int(self.INV[v[c]]); self.piv.append((c,self.MUL[iv,v],{k:int(self.F.mul[iv][x]) for k,x in cb.items()})); return None
    def solve(self,target):
        v,cb=self.reduce(target,{'TARGET':1})
        return (not np.any(v)), cb
