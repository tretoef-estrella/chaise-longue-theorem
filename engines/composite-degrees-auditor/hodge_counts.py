# |B| (Hodge characters) vs |D| = Q_k(m) (pair type), by multiset enumeration. Own code (regla284).
import itertools, math, collections, sys
from math import gcd, factorial
exec(open('sellado.py').read().split('print(')[0])
def counts(m,k):
    N=2*k+2; units=[t for t in range(1,m) if gcd(t,m)==1]
    B=0; D=0
    for ms in itertools.combinations_with_replacement(range(1,m),N):
        if sum(ms)%m: continue
        c=collections.Counter(ms); mult=factorial(N)
        for v in c.values(): mult//=factorial(v)
        if all(sum((t*a)%m for a in ms)==m*(k+1) for t in units): B+=mult
        if all(c[a]==c[m-a] for a in c): D+=mult
    return B,D
for m,k in [(9,1),(9,2),(9,3),(15,1),(21,1),(45,1),(35,1),(55,1),(77,1),(25,1),(49,1),(15,2),(35,2),(25,2),(27,1)]:
    B,D=counts(m,k); print(f"(k,m)=({k},{m}) |B|={B} |D|={D} Q={Q(k,m)} B-D={B-D}",flush=True)
