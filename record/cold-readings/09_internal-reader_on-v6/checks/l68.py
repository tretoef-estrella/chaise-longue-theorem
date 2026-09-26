# Lemma 6.8: |Gamma_J| = sum_c N1(c) prod N_zeta(c), using additive Z/m notation
import itertools, sys
from collections import Counter
from math import comb
from functools import lru_cache
sys.path.insert(0,'.')
from q import Q, Nbal
def Nph(a,q): return Nbal(a+1,q)
def gamma(m,n):
    cnt=0
    for a in itertools.product(range(m),repeat=n+1):
        if 0 in a: continue
        a0=(-sum(a))%m
        if a0==0: continue
        C=Counter(a+(a0,))
        if all(C[x]==C[(-x)%m] for x in C): cnt+=1
    return cnt
def N1(size,has0,q):
    # tuples closed under inversion in mu_q\{1}
    if size%2: return 0
    kp=size//2
    if has0: return Q(kp-1,q) if kp>=1 else 0
    # 2k' tuples in T closed: = |Z_{emptyset}|
    # count directly: number of 2k'-tuples over q-1 elems with involution closed
    h=(q-1)//2
    # EGF: I0(2x)^h coefficient * (2k')!
    from fractions import Fraction
    from math import factorial
    poly={0:Fraction(1)}
    base={2*b:Fraction(1,factorial(b)**2) for b in range(kp+1)}
    for _ in range(h):
        new={}
        for e,c in poly.items():
            for e2,c2 in base.items():
                if e+e2<=size: new[e+e2]=new.get(e+e2,0)+c*c2
        poly=new
    return int(poly.get(size,0)*factorial(size))
def blocksum(m,n,p):
    q=1
    while m%(q*p)==0: q*=p
    r=m//q
    tot=0
    for c in itertools.product(range(r),repeat=n+1):
        c0=(-sum(c))%r
        cols=(c0,)+c
        C1=[i for i in range(n+2) if cols[i]==0]
        val=N1(len(C1),0 in C1,q)
        if val==0: continue
        for z in range(1,(r+1)//2):
            A=[i for i in range(n+2) if cols[i]==z]; B=[i for i in range(n+2) if cols[i]==(r-z)%r]
            if len(A)!=len(B): val=0;break
            if 0 in A or 0 in B: val*=Nph(len(A)-1,q)
            else: val*=Nbal(len(A),q)
        tot+=val
    return tot
for m,n in [(15,2),(21,2),(45,2),(15,4),(33,2),(35,2)]:
    g=gamma(m,n) if (m**(n+1))<3e6 else None
    print(m,n,"gamma",g,"Q",Q(n//2,m),[ (p,blocksum(m,n,p)) for p in set(x for x in [3,5,7,11] if m%x==0)])
