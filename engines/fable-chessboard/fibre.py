# INFORME_8: |W_mu(n)| from the generating function of MISION_8 §1 (exact, fractions)
from fractions import Fraction as Fr
from math import factorial
import sys
def series(coeffs_fn, N):  # list of coefficients 0..N
    return [coeffs_fn(k) for k in range(N+1)]
def mul(a,b):
    N=len(a)-1; c=[Fr(0)]*(N+1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b):
            if i+j>N: break
            c[i+j]+=x*y
    return c
def I(m,N):
    c=[Fr(0)]*(N+1)
    for b in range(N+1):
        k=2*b+m
        if k>N: break
        c[k]=Fr(1, factorial(b)*factorial(b+m))
    return c
def E(par,N):
    c=[Fr(0)]*(N+1)
    for k in range(N+1):
        if k%2==par: c[k]=Fr(1,factorial(k))
    return c
def W(mu,n,q):
    h=(q-1)//2; l=len(mu); s=sum(mu)
    if s>n or l>h: return 0
    N=n; c=E((n-s)%2,N)
    for m in mu: c=mul(c,I(m,N))
    for _ in range(h-l): c=mul(c,I(0,N))
    v=c[n]*factorial(n); assert v.denominator==1; return int(v)
if __name__=="__main__":
    q=int(sys.argv[1]) if len(sys.argv)>1 else 9
    # gates of §1 at q=9
    if q==9:
        gates={((),4):217,((1,),5):855,((1,1),4):84,((2,),4):46,((1,),4):88,((1,),8):227144,((1,),9):1930329,((1,1),8):204456,((2,),8):130984}
        for (mu,n),v in gates.items(): assert W(mu,n,q)==v,(mu,n,W(mu,n,q),v)
        print("gates §1 at q=9: 9/9 OK")
    for mu in [(),(1,),(2,),(3,),(4,),(1,1),(2,1),(3,1),(4,1),(2,2),(3,2),(1,1,1),(2,1,1),(3,1,1),(2,2,1),(1,1,1,1),(2,1,1,1),(1,1,1,1,1)]:
        print("q=%d mu=%-12s"%(q,str(mu)), [W(mu,n,q) for n in range(0,11)])
