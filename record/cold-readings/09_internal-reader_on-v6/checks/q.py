from fractions import Fraction
from math import factorial, comb
from itertools import product
def Q(k,q):
    h=(q-1)//2; N=2*k+2
    # coefficient of x^N in I0(2x)^h
    poly={0:Fraction(1)}
    base={2*b:Fraction(1,factorial(b)**2) for b in range(N//2+1)}
    for _ in range(h):
        new={}
        for e,c in poly.items():
            for e2,c2 in base.items():
                if e+e2<=N: new[e+e2]=new.get(e+e2,0)+c*c2
        poly=new
    return int(poly.get(N,0)*factorial(N))
for q in [3,5,7,9,11,13,25,27]:
    print(q,[Q(k,q) for k in range(1,6)])
print("Q2(15)",Q(2,15),"Q2(21)",Q(2,21),"Q1(125)",Q(1,125),"Q1(49)",Q(1,49),"Q1(25)",Q(1,25))
def Nbal(a,q):
    # sum over compositions of a into q parts of multinomial^2
    from functools import lru_cache
    @lru_cache(None)
    def f(a,q):
        if q==0: return 1 if a==0 else 0
        return sum(comb(a,c)**2*f(a-c,q-1) for c in range(a+1))
    return f(a,q)
print([Nbal(a,3) for a in range(1,6)],[Nbal(2,q) for q in [3,5,7,9,11]])
print("Nbal(5,4)?",Nbal(4,5),Nbal(3,13),Nbal(5,3))
