import itertools, numpy as np, sys
from math import gcd, factorial
from q import Q
def B(k,m):
    N=2*k+2
    units=[t for t in range(1,m) if gcd(t,m)==1 and t<=m-t]
    it=itertools.combinations_with_replacement(range(1,m),N)
    tot=0; pair=0
    while True:
        ch=list(itertools.islice(it,200000))
        if not ch: break
        A=np.array(ch,dtype=np.int64)
        ok=np.ones(len(A),bool)
        for t in units:
            ok&=((A*t)%m).sum(1)==m*(k+1)
        A=A[ok]
        for row in A:
            c=np.bincount(row,minlength=m)
            mult=factorial(N)
            for x in c: mult//=factorial(int(x))
            tot+=mult
            if all(c[a]==c[m-a] for a in range(1,m)): pair+=mult
    return tot,pair
for k,m in [(1,9),(2,9),(1,15),(1,21),(1,27),(1,45),(1,81),(1,25),(1,35),(1,49),(1,55),(1,77),(1,121),(2,15),(2,25),(2,35),(2,5),(2,7)]:
    b,pr=B(k,m); print(k,m,"B",b,"pair",pr,"Q",Q(k,m),"diff",b-Q(k,m),flush=True)
