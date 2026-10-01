# Explicit, j-independent rank rule vs count-ordered rule, all profiles b.
import itertools
from functools import lru_cache
def steps(m):
    out=[tuple([0]*m)]
    for i in range(m):
        for s in (1,-1):
            v=[0]*m; v[i]=s; out.append(tuple(v))
    return out
def sub(b,c): return tuple(x-y for x,y in zip(b,c))
def key(b,c):
    # backward from b to child b-c
    if all(x==0 for x in c): return (1,0)
    i=[k for k in range(len(c)) if c[k]!=0][0]
    bi=b[i]; ch=bi-c[i]
    if abs(ch)<abs(bi): return (0,-abs(bi))     # child closer: reduce largest first
    return (2,abs(bi))                           # child farther: grow smallest first
def make(q):
    m=(q-1)//2; S=steps(m)
    @lru_cache(None)
    def N(j,b):
        if j==0: return 1 if all(x==0 for x in b) else 0
        if sum(abs(x) for x in b)>j: return 0
        return sum(N(j-1,sub(b,c)) for c in S)
    @lru_cache(None)
    def F(j,b,mode):
        if j==0: return (1,) if all(x==0 for x in b) else ()
        ch=[(c,sub(b,c)) for c in S]
        if mode=='count': ch.sort(key=lambda x:-N(j-1,x[1]))
        else: ch.sort(key=lambda x:key(b,x[0]))
        poly={}
        for r,(c,bb) in enumerate(ch):
            if N(j-1,bb)==0: continue
            for d,a in enumerate(F(j-1,bb,mode)): poly[d+r]=poly.get(d+r,0)+a
        L=max(poly)+1 if poly else 0
        return tuple(poly.get(d,0) for d in range(L))
    return m,N,F
bad=0;tot=0
for q,nmax in [(3,10),(5,8),(7,6),(9,5),(11,4)]:
    m,N,F=make(q)
    for n in range(1,nmax+1):
        for b in itertools.product(range(-n,n+1),repeat=m):
            if N(n,b)==0: continue
            tot+=1
            if F(n,b,'count')!=F(n,b,'key'):
                bad+=1
                if bad<10: print('DIFF',q,n,b,F(n,b,'count'),F(n,b,'key'))
    print('q',q,'done')
print('profiles',tot,'disagreements',bad)
