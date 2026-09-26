# Worked example for v7 §6: (k,m)=(1,15), both primes. Block products of Lemma 6.8, grouped by type.
from itertools import product
from math import comb, factorial
from collections import Counter, defaultdict
def Nbal(a,q):
    # sum over compositions of a into q parts of multinomial^2
    from functools import lru_cache
    @lru_cache(None)
    def f(a,parts):
        if parts==0: return 1 if a==0 else 0
        return sum((comb(a,c)**2)*f(a-c,parts-1) for c in range(a+1))
    return f(a,q)
def Nph(a,q): return Nbal(a+1,q)
def Q(k,q):
    # N-tuples in mu_q\{1} closed under inversion, N=2k+2
    N=2*k+2; h=(q-1)//2
    from functools import lru_cache
    @lru_cache(None)
    def g(n,cls):
        if cls==0: return 1 if n==0 else 0
        return sum(comb(n,2*b)*comb(2*b,b)*g(n-2*b,cls-1) for b in range(n//2+1))
    return g(N,h)
def run(m,p):
    q=1
    while m%(q*p)==0: q*=p
    r=m//q
    n=2; N=n+2
    tot=0; types=Counter(); contrib=defaultdict(int)
    for c in product(range(r),repeat=n+1):  # exponents of zeta
        c0=(-sum(c))%r; cols=[c0]+list(c)
        C1=[i for i in range(N) if cols[i]==0]
        if len(C1)%2: continue
        ok=True; pairs=[]
        for z in range(1,(r-1)//2+1):
            A=[i for i in range(N) if cols[i]==z]; B=[i for i in range(N) if cols[i]==(r-z)%r]
            if len(A)!=len(B): ok=False;break
            if A or B: pairs.append((A,B))
        if not ok: continue
        k1=len(C1)//2
        if 0 in C1: n1=Q(k1-1,q) if k1>=1 else 1
        else: n1=Q(k1-1,q) if k1>=1 else 1
        prod_=n1; desc=[f"C1={len(C1)}{'∋0' if 0 in C1 else ''}"]
        for A,B in pairs:
            if 0 in A or 0 in B:
                a=min(len(A),len(B))-0; a=len(B)-1 if 0 in B else len(A)-1
                v=Nph(a,q); desc.append(f"ph{a}")
            else:
                v=Nbal(len(A),q); desc.append(f"bal{len(A)}")
            prod_*=v
        key=' '.join(desc)
        types[key]+=1; contrib[key]+=prod_; tot+=prod_
    print(f"(k,m,p)=(1,{m},{p}) q={q} r={r} compatible={sum(types.values())} total={tot} Q_1(m)={3*(m-1)*(m-2)}")
    for kk in sorted(types): print(f"   {kk:22s} colourings={types[kk]:4d} each={contrib[kk]//types[kk]:5d} sum={contrib[kk]}")
run(15,3); run(15,5)
