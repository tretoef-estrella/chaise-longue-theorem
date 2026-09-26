# (1,1): y_c^2 D_{j;cd} = y_j^{q-2} e_{n-1}(y) - y_j^{q-1}(y_c+y_d) x_{Y\j} + y_c (phi_{jd} - phi_{jc})   EXACT over ZZ (no box needed)
# and G_r(A;B)|_{z=0} = x_A^{q-1} x_{[n-1]\(A u B)}  (row-0 identity), r = 1,2,3; raise identity lowest z-term.
from grepy_polys import add, mul, mono, e_, sc
ok=tot=0
for q in (9,27,81):
  for n in range(4,10):
    nv=n; ys=list(range(n)); j,c,d=0,1,2; f=n-2
    Y=[i for i in ys if i not in (c,d)]
    D=mul(mono(nv,{j:q-2}),e_(nv,Y,f-1))
    phi=lambda jj,ll: mul(mono(nv,{jj:q-2}),e_(nv,[i for i in ys if i!=ll],f))
    lhs=mul(mono(nv,{c:2}),D)
    xYj={tuple(1 if (i in Y and i!=j) else 0 for i in range(nv)):1}
    rhs=add(add(mul(mono(nv,{j:q-2}),e_(nv,ys,n-1)), sc(mul(mul(mono(nv,{j:q-1}),add(mono(nv,{c:1}),mono(nv,{d:1}))),xYj),-1)), mul(mono(nv,{c:1}),add(phi(j,d),phi(j,c),-1)))
    tot+=1; ok+= (add(lhs,rhs,-1)=={})
print('y_c^2 D identity (1,1): %d/%d (q=9,27,81; n=4..9)'%(ok,tot))
# row-0 identity for the tower
ok=tot=0
import itertools
for q in (9,27):
  for n in range(4,10):
    for r in (1,2,3):
      if 2*r>n-1: continue
      ys=list(range(n)); z=n-1; A=list(range(r)); B=list(range(r,2*r))
      V=[i for i in ys if i not in B]
      G=mul(mono(n,{i:q-2 for i in A}),e_(n,V,n-r-1))
      G0={m:v for m,v in G.items() if m[z]==0}
      tgt={tuple((q-1) if i in A else (1 if (i not in B and i!=z) else 0) for i in range(n)):1}
      tot+=1; ok+=(G0==tgt)
      # raise: z in A  -> lowest z-term z^{q-2} x_{A\z}^{q-1} x_{[n-1]\(AuB)}
      A2=list(range(r-1))+[z]; B2=list(range(r-1,2*r-1)); V2=[i for i in ys if i not in B2]
      G2=mul(mono(n,{i:q-2 for i in A2}),e_(n,V2,n-r-1)); lowz=min(m[z] for m in G2)
      low={m:v for m,v in G2.items() if m[z]==lowz}
      tgt2={tuple((q-2) if i==z else ((q-1) if i in A2 else (1 if i not in B2 else 0)) for i in range(n)):1}
      tot+=1; ok+=(low==tgt2)
print('tower row-0 and raise identities: %d/%d'%(ok,tot))
