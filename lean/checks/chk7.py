import sympy as sp, itertools
fails=0
ys=sp.symbols('y1:7')
def D(a,b,q): return sum((-1)**i*a**i*b**(q-2-i) for i in range(q-1))
def Delta(B):
    B=sorted(B); r=sp.Integer(1)
    for c in range(len(B)):
        for d in range(c+1,len(B)): r*= (ys[B[d]]-ys[B[c]])
    return sp.expand(r)
for q in (3,5,7,9):
    a,b=ys[0],ys[1]; d=sp.expand(D(a,b,q))
    if sp.expand((a+b)*d-(b**(q-1)-a**(q-1)))!=0: fails+=1
    if sp.expand(D(b,a,q)+d)!=0: fails+=1
    P=sp.Poly(d,a)
    for t in range(q-1):
        if sp.expand(P.coeff_monomial(a**(q-2-t))-(-1)**(t+1)*b**t)!=0: fails+=1
for r in range(1,6):
    S=list(range(r))
    for t in range(r):
        s=sum((-1)**(r+c+1)*Delta([x for x in S if x!=S[c]])*ys[S[c]]**t for c in range(r))  # c 0-based -> (-1)^{r+(c+1)}
        target=0 if t<=r-2 else Delta(S)
        if sp.expand(s-target)!=0: fails+=1; print('ii fail',r,t)
for nb in range(0,5):
    B=list(range(1,nb+1)); lhs=Delta([0]+B); rhs=sp.expand(sp.prod([ys[c]-ys[0] for c in B])*Delta(B))
    if sp.expand(lhs-rhs)!=0: fails+=1
    P=sp.Poly(lhs,ys[0])
    if P.degree()!=nb or sp.expand(P.coeff_monomial(ys[0]**nb)-(-1)**nb*Delta(B))!=0: fails+=1
print('fails',fails)
