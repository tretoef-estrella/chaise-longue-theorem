# Independent computation of (S): dim_{F_3} (D_J : J in J) C  for C = F_3[y_1..y_{2k+1}]/(y_i^{q-1})
import sys, itertools, time
from ideal import *

def D(a,b,m,q,p=3):
    # D(y_a,y_b) = sum_{u=0}^{q-2} (-1)^u y_a^u y_b^{q-2-u}
    r={}
    for u in range(q-1):
        k=[0]*m; k[a]+=u; k[b]+=q-2-u
        r[tuple(k)]=(r.get(tuple(k),0)+(-1)**u)%p
    return {k:v for k,v in r.items() if v}

def matchings(elems):
    if not elems: yield []; return
    a=elems[0]
    for i in range(1,len(elems)):
        b=elems[i]
        rest=elems[1:i]+elems[i+1:]
        for M in matchings(rest): yield [(a,b)]+M

def S_gens(k,q,p=3):
    m=2*k+1; e=q-1
    gens=[]
    for J in matchings(list(range(0,2*k+2))):
        g=const(1,m)
        for (a,b) in J:
            if a==0: continue
            g=pmul(g,D(a-1,b-1,m,q,p),p,e)
        gens.append(g)
    return m,e,gens

if __name__=="__main__":
    k=int(sys.argv[1]); q=int(sys.argv[2])
    m,e,gens=S_gens(k,q)
    t=time.time()
    tot,gr=ideal_dim(m,e,3,gens)
    print(f"(k,q)=({k},{q}): dim (D_J)C = {tot}; graded = {[gr[d] for d in sorted(gr) if gr[d]]}; {time.time()-t:.1f}s",flush=True)
