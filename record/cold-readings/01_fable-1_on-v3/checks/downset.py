# Independent test of Theorem 5.3: dim V_Lambda >= |Z_Lambda| for EVERY weak-dominance down-set Lambda of Par_m, small (q,m).
# Also tests P1/P2/P3 consequences: |Z_Lambda| = sum_i |Z_{Lambda_i}| and Lambda_i down-sets, and V_{Lambda_i} ⊆ W_{q-2-i}(V_Lambda) is NOT tested here (only the dimension inequality).
import sys, itertools, time
import numpy as np
from ideal import *
from p2test import partitions_upto, leq, options, sort_desc
from sform import D, matchings

def Par(m,h):
    return [lam for lam in partitions_upto(m,h) if (sum(lam)-m)%2==0]

def downsets(P):
    # enumerate all down-sets (antichain generated); brute force over subsets for small P
    P=list(P); n=len(P)
    below={i:[j for j in range(n) if leq(P[j],P[i])] for i in range(n)}
    res=[]
    for mask in range(1<<n):
        ok=True
        for i in range(n):
            if mask>>i&1:
                for j in below[i]:
                    if not mask>>j&1: ok=False;break
            if not ok: break
        if ok: res.append(frozenset(P[i] for i in range(n) if mask>>i&1))
    return res

def conj(lam):
    return [sum(1 for x in lam if x>=c) for c in range(1,(lam[0] if lam else 0)+1)]

def vandermonde(B,m,p=3):
    # Delta(B) = prod_{c<c'} (y_{b_c'} - y_{b_c}), B sorted
    g=const(1,m)
    for i in range(len(B)):
        for j in range(i+1,len(B)):
            g=pmul(g,padd(var(B[j],m),pmul(const(-1,m),var(B[i],m),p),p),p)
    return g

def set_partitions_into_blocks(elems,sizes):
    # yield lists of blocks (as sorted tuples) with given sizes, blocks are labelled (ordered) by column
    if not sizes:
        if not elems: yield []
        return
    s=sizes[0]
    for B in itertools.combinations(elems,s):
        rest=[x for x in elems if x not in B]
        for tail in set_partitions_into_blocks(rest,sizes[1:]):
            yield [B]+tail

def tight_pattern_products(lam,m,q,p=3):
    e=q-1
    idx=list(range(m))
    cols=conj(lam)
    npairs=(m-sum(lam))//2
    gens=[]
    for pairset in itertools.combinations(idx,2*npairs):
        rest=[x for x in idx if x not in pairset]
        for P in matchings(list(pairset)):
            gP=const(1,m)
            for (a,b) in P: gP=pmul(gP,D(a,b,m,q,p),p,e)
            for blocks in set_partitions_into_blocks(rest,cols):
                g=gP
                for B in blocks: g=pmul(g,vandermonde(list(B),m,p),p,e)
                if g: gens.append(g)
    return gens

def lam_of(M,h):
    # M tuple of values in {±1..±h}
    parts=[]
    for c in range(1,h+1):
        a=M.count(c); b=M.count(-c)
        if a!=b: parts.append(abs(a-b))
    return sort_desc(parts)

def Zcount(Lam,m,h):
    T=[c for c in range(1,h+1)]+[-c for c in range(1,h+1)]
    return sum(1 for M in itertools.product(T,repeat=m) if lam_of(M,h) in Lam)

if __name__=="__main__":
    q=int(sys.argv[1]); m=int(sys.argv[2]); h=(q-1)//2; e=q-1
    P=Par(m,h)
    DS=downsets(P)
    print(f"q={q} m={m}: Par_m={P}, #down-sets={len(DS)}")
    # precompute generators per lambda
    gens={lam:tight_pattern_products(lam,m,q) for lam in P}
    # precompute lambda(M) counts
    T=[c for c in range(1,h+1)]+[-c for c in range(1,h+1)]
    cnt={}
    for M in itertools.product(T,repeat=m):
        l=lam_of(M,h); cnt[l]=cnt.get(l,0)+1
    assert sum(cnt.values())==(q-1)**m
    bad=0
    for Lam in DS:
        G=[g for lam in Lam for g in gens[lam]]
        dimV=ideal_dim(m,e,3,G)[0] if G else 0
        Z=sum(cnt.get(l,0) for l in Lam)
        flag="" if dimV>=Z else "  <-- VIOLATION"
        if dimV!=Z: flag+="  (not equal)"
        if dimV<Z: bad+=1
        print(f"  Lambda={sorted(Lam,key=lambda x:(sum(x),x))}: dim V={dimV}, |Z|={Z}{flag}")
    print("violations:",bad)
