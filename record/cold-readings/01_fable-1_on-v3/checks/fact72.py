# Fact 7.2 and the q=3,k=2 subfamily statement; and the table of §3.
import itertools, sys
from fractions import Fraction
from math import factorial
from ideal import *
from sform import D, matchings

def Q(k,q):
    N=2*k+2; h=(q-1)//2
    I0=[Fraction(0)]*(N+1)
    for b in range(N//2+1): I0[2*b]=Fraction(1,factorial(b)**2)
    r=[Fraction(1)]+[Fraction(0)]*N
    for _ in range(h):
        c=[Fraction(0)]*(N+1)
        for i in range(N+1):
            if r[i]:
                for j in range(N+1-i): c[i+j]+=r[i]*I0[j]
        r=c
    return factorial(N)*r[N]

print("Table §3 recomputed:")
for q in [3,9,27,81]:
    print(" q=%d:"%q,[Q(k,q) for k in range(0,7) if (q,k) not in [(27,6),(81,4),(81,5),(81,6)]])

def GammaK(k,q,K):
    # tuples in mu_q\{1} ~ integers 1..q-1 (exponents), inversion = negation mod q; count (a_1..a_{2k+1}) with some J in K: a_{j_i}+a_{k_i} ≡ 0 for i>=1
    m=2*k+1; cnt=0
    for a in itertools.product(range(1,q),repeat=m):
        ok=False
        for J in K:
            if all((a[x-1]+a[y-1])%q==0 for (x,y) in J if x!=0): ok=True;break
        if ok: cnt+=1
    return cnt

def dimK(k,q,K):
    m=2*k+1; e=q-1; gens=[]
    for J in K:
        g=const(1,m)
        for (a,b) in J:
            if a==0: continue
            g=pmul(g,D(a-1,b-1,m,q,3),3,e)
        gens.append(g)
    return ideal_dim(m,e,3,gens)[0]

allJ=[tuple(J) for J in matchings(list(range(6)))]
ex1=((0,1),(2,3),(4,5)); ex2=((0,2),(1,5),(3,4))
K=[J for J in allJ if J not in (ex1,ex2)]
assert len(K)==13
print("Fact 7.2 (q=9,k=2, 13 matchings): dim(D_J:J in K)C =",dimK(2,9,K)," |Gamma_K| =",GammaK(2,9,K))

# q=3, k=2: all non-empty subfamilies
import numpy as np
m=5; e=2
vecs={}
monos=list(itertools.product(range(2),repeat=5)); idx={mo:i for i,mo in enumerate(monos)}
gen={}
for J in allJ:
    g=const(1,m)
    for (a,b) in J:
        if a==0: continue
        g=pmul(g,D(a-1,b-1,m,3,3),3,e)
    gen[J]=g
# closure of a set of generators: all monomial multiples (squarefree)
def dim_sub(Ks):
    rows=[]
    for J in Ks:
        g=gen[J]
        for mo in monos:
            new={}
            for kk,c in g.items():
                s=tuple(x+y for x,y in zip(kk,mo))
                if max(s)<2: new[s]=c
            if new:
                v=np.zeros(32,dtype=np.int64)
                for kk,c in new.items(): v[idx[kk]]=c
                rows.append(v)
    return rank_mod_p(np.array(rows),3)
# Gamma_K at q=3: values in {1,2}, a_x+a_y ≡ 0 mod 3
pts=list(itertools.product([1,2],repeat=5))
sat={J:frozenset(i for i,a in enumerate(pts) if all((a[x-1]+a[y-1])%3==0 for (x,y) in J if x!=0)) for J in allJ}
fails=0; worst=0; leq_ok=True; total=0
for r in range(1,16):
    for Ks in itertools.combinations(allJ,r):
        total+=1
        d=dim_sub(Ks); g=len(frozenset().union(*[sat[J] for J in Ks]))
        if d>g: leq_ok=False
        if d<g: fails+=1; worst=max(worst,g-d)
print(f"q=3,k=2: {total} non-empty subfamilies; (S)-analogue fails in {fails}, worst deficit {worst}; '<=' always holds: {leq_ok}")
