exec(open('chk8.py').read().split('fails=checks=0')[0])
import itertools, math
from fractions import Fraction
def matchings(s):
    if not s: yield []; return
    a=s[0]
    for b in s[1:]:
        for r in matchings([x for x in s if x not in (a,b)]): yield [(a,b)]+r
def Qk(k,q):
    N=2*k+2; h=(q-1)//2; tot=Fraction(0)
    for bs in itertools.product(range(N//2+1),repeat=h):
        if 2*sum(bs)==N: tot+=Fraction(math.factorial(N),math.prod(math.factorial(b)**2 for b in bs))
    return int(tot)
def nu(M,h): return sum(min(M.count(u),M.count(-u)) for u in range(1,h+1))
for k,q in ((0,3),(0,5),(1,3),(1,5),(1,7),(2,3),(2,5),(3,3)):
    n=2*k+1; h=(q-1)//2; T=[s*u for u in range(1,h+1) for s in (1,-1)]
    gens=[]
    for J in matchings(list(range(2*k+2))):
        g=const(n)
        for a,b in J:
            if a==0 or b==0: continue
            g=pmul(g,D(a-1,b-1,n,q),q)
        gens.append(g)
    V,M,idx=ideal(gens,n,q)
    G=sum(1 for M_ in itertools.product(T,repeat=n) if nu(list(M_),h)==k)
    closed=sum(1 for M_ in itertools.product(T,repeat=n+1) if all(M_.count(u)==M_.count(-u) for u in range(1,h+1)))
    print(k,q,'dim',len(V),'Q',Qk(k,q),'Gamma',G,'closed',closed, 'OK' if len(V)>=Qk(k,q)==G==closed else 'FAIL')
