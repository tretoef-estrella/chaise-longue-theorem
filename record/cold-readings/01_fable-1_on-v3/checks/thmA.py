# Independent test of Theorem A: dim_F F[x_1..x_n]/(e_odd; x_i^q) vs N_q(n) = n! [y^n] e^y I_0(2y)^h, over F_p for several p.
import sys, itertools
from fractions import Fraction
from math import factorial
from ideal import *

def N_q(n,q):
    h=(q-1)//2
    # series coefficients up to y^n
    I0=[Fraction(0)]*(n+1)
    for b in range(0,n//2+1): I0[2*b]=Fraction(1,factorial(b)**2)
    ey=[Fraction(1,factorial(i)) for i in range(n+1)]
    def mul(a,b):
        c=[Fraction(0)]*(n+1)
        for i in range(n+1):
            if a[i]==0: continue
            for j in range(n+1-i): c[i+j]+=a[i]*b[j]
        return c
    r=ey
    for _ in range(h): r=mul(r,I0)
    return factorial(n)*r[n]

def e_j(j,n,p):
    r={}
    for S in itertools.combinations(range(n),j):
        k=[0]*n
        for i in S: k[i]=1
        r[tuple(k)]=1%p
    return r

def dimA(n,q,p):
    gens=[e_j(j,n,p) for j in range(1,n+1,2)]
    # x_i^q is zero in the box ring with e=q, so quotient by (e_odd) inside F[x]/(x^q)
    tot,gr=ideal_dim(n,q,p,gens)
    return q**n-tot

if __name__=="__main__":
    for p in [3,5,7,2]:
        for q in [1,3,5,7,9]:
            for n in range(0,5):
                if q**n>20000: continue
                d=dimA(n,q,p); Nn=N_q(n,q)
                flag="" if d==Nn else "  <-- MISMATCH"
                print(f"p={p} q={q} n={n}: dim={d}  N_q(n)={Nn}{flag}")
