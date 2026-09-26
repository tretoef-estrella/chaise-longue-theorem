from fractions import Fraction
from math import factorial as f
def N(a,q):
    # (a!)^2 [x^a] (sum_c x^c/(c!)^2)^q
    poly=[Fraction(1,f(c)**2) for c in range(a+1)]
    res=[Fraction(1)]+[Fraction(0)]*a
    for _ in range(q):
        new=[Fraction(0)]*(a+1)
        for i,x in enumerate(res):
            if x==0: continue
            for j,y in enumerate(poly):
                if i+j<=a: new[i+j]+=x*y
        res=new
    return int(res[a]*f(a)**2)
def Q(k,m):
    Nn=2*k+2; h=(m-1)//2
    poly=[Fraction(1,f(b)**2) if e%2==0 else Fraction(0) for e in range(Nn+1) for b in [e//2]]
    res=[Fraction(1)]+[Fraction(0)]*Nn
    for _ in range(h):
        new=[Fraction(0)]*(Nn+1)
        for i,x in enumerate(res):
            if x==0: continue
            for j,y in enumerate(poly):
                if i+j<=Nn: new[i+j]+=x*y
        res=new
    return int(res[Nn]*f(Nn))
print("bipartite N(a,q) balanced; N'(a,q)=N(a+1,q)")
for a,q in [(5,3),(4,5),(3,7),(2,11),(2,13),(2,25),(2,27),(1,25),(1,27),(3,9),(4,3)]:
    print(a,q,"N=",N(a,q),"N'=",N(a+1,q))
print("Q_k(m) composite")
for k,m in [(1,15),(1,21),(1,33),(1,35),(1,39),(1,45),(1,51),(1,55),(1,63),(2,15),(2,21),(2,35),(3,15),(2,45)]:
    print(k,m,Q(k,m), "literal quotient m^{2k+1}-Q =", m**(2*k+1)-Q(k,m))
