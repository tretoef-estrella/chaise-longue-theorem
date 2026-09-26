# grepy_tres_letras.py — the THREE-LETTER structure behind the open raise rows (auditor, 2026-09-23), over ZZ, mod box.
# Parent (1^l) at n+1 (vars y_0..y_{n-1}, z=y_n); a=y0, b=y1, c=y2, P''=y\{a,b,c};  U := a^{q-l} sum_{i<l} a^i e_{n-3-i}(P'').
# Claims: (1) phi_ab(parent) == (a+c)(a+z) U  mod box;  (2) phi_ac == (a+b)(a+z) U;  (3) phi_az == (a+b)(a+c) U  (z-free!);
#         (4) the child's layer monomial T_{a;bc} := a^{q-1} x_{P''}  ==  a^{l-1} U  mod box.   Estimate: < 30 s, < 100 MB.
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grepy_polys import add,mul,mono,e_,phi,inbox
ok=tot=0
for q in (9,27,81):
  for l in range(1,min(4,(q-1)//2)+1):
    for n in range(max(l+2,3),10):
      nv=n+1; ys=list(range(n)); z=n; a,b,c=0,1,2; Pp=ys[3:]
      U={}
      for i in range(l): U=add(U,mul(mono(nv,{a:q-l+i}),e_(nv,Pp,n-3-i)))
      lin=lambda u,v: add(mono(nv,{u:1}),mono(nv,{v:1}))
      def box0(P): return all(inbox(m,q) for m in P)
      pab=phi(nv,ys+[z],q,l,n-1,a,b); pac=phi(nv,ys+[z],q,l,n-1,a,c); paz=phi(nv,ys+[z],q,l,n-1,a,z)
      r1=box0(add(pab,mul(mul(lin(a,c),lin(a,z)),U),-1)); r2=box0(add(pac,mul(mul(lin(a,b),lin(a,z)),U),-1))
      r3=box0(add(paz,mul(mul(lin(a,b),lin(a,c)),U),-1))
      T=mono(nv,{a:q-1,**{p:1 for p in Pp}})
      r4=box0(add(T,mul(mono(nv,{a:l-1}),U),-1))
      tot+=4; ok+=r1+r2+r3+r4
      if not (r1 and r2 and r3 and r4): print('FAIL',q,l,n,r1,r2,r3,r4)
print('three-letter identities (1)-(4):',ok,'/',tot); print('FIN-OK')
