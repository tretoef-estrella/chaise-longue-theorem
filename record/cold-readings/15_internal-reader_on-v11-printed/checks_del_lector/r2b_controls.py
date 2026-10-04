# R2b (Grepy Tinta): replacement controls for R2.
import sys, numpy as np
sys.argv=['x']
import importlib.util
src=open('checks/r2_literal.py').read().split("print('== P2.5")[0]
exec(src)
print('P2b.1 (1,3,3) sign=+1 :',cell(1,3,3,sign=1),' (true value 6)')
def psi_eq(J,m,n1):
    A=np.zeros((m,)*n1,dtype=np.int64); A[(0,)*n1]=1
    for (j,kk) in J:
        A=np.roll(A,1,axis=kk-1)-A
        if j!=0:
            B=np.zeros_like(A)
            for c in range(m): B+=np.roll(np.roll(A,c,axis=j-1),-c,axis=kk-1)
            A=B
    return A
for (k,m,p) in [(1,4,2),(1,6,3),(1,6,2)]:
    n1=2*k+1; Js=list(matchings(range(n1+1)))
    gens=[flat(psi_eq(J,m,n1),n1) for J in Js]
    d=ideal_dim_p2(gens,m,n1) if p==2 else ideal_dim_odd(gens,m,n1,p)
    print('P2b.2',(k,m,p),'with phi(t_j t_k^-1): dim =',d)
