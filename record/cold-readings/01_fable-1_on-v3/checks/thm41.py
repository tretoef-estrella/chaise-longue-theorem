# Theorem 4.1: lex leading monomials (y_1 > ... > y_n') of (D_J)C at q=3 are exactly y_U, U in the set of paths never below -1.
import itertools, numpy as np
from ideal import *
from sform import D, matchings
def paths(n):
    res=[]
    for U in itertools.product([0,1],repeat=n):
        h=0; ok=True
        for i in range(n):
            h+= 1 if U[i] else -1
            if h<-1: ok=False;break
        if ok: res.append(U)
    return set(res)
for k in range(1,5):
    m=2*k+1; e=2
    monos=list(itertools.product(range(2),repeat=m))
    # lex order with y_1 largest: sort exponent tuples descending lexicographically
    monos.sort(reverse=True); idx={mo:i for i,mo in enumerate(monos)}
    rows=[]
    for J in matchings(list(range(2*k+2))):
        g=const(1,m)
        for (a,b) in J:
            if a==0: continue
            g=pmul(g,D(a-1,b-1,m,3,3),3,e)
        for mo in monos:
            new={}
            for kk,c in g.items():
                s=tuple(x+y for x,y in zip(kk,mo))
                if max(s)<2: new[s]=c
            if new:
                v=np.zeros(len(monos),dtype=np.int64)
                for kk,c in new.items(): v[idx[kk]]=c
                rows.append(v)
    B=rowspace_basis_mod_p(np.array(rows),3)
    LM=set()
    for row in B:
        j=np.nonzero(row)[0][0]; LM.add(monos[j])
    P=paths(m)
    print(f"k={k}: dim={len(B)}, #LM={len(LM)}, #paths={len(P)}, LM==paths: {LM==P}")
