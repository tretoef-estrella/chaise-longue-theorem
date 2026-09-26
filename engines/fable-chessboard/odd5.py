# INFORME_9 STEP 2: m=1, n odd. Check on all points of W_(1)(n): (O)  s + tau + [u!=0] y_l^(q-2) Pi_P - [u!=0][y_l=0] e_{n-3}(P) == 0
# and the coefficient identity (R1): u y_l e_{n-3}(P) + (u y_l + u + y_l) Pi_P == 0.
import itertools, sys, numpy as np
from fq import Fq
def run(n,q):
    F=Fq(q); j,l=0,1; P=[i for i in range(n) if i not in (j,l)]
    W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[1])]
    bad1=bad2=0
    for y in W:
        u=y[j]; yl=y[l]; PiP=F.p(*[y[p] for p in P]); e1=F.esym([y[p] for p in P], n-3)
        s=F.mul[F.pw(u,q-2)][F.esym([y[i] for i in range(n) if i!=l], n-2)]
        tau=F.mul[F.pw(u,q-1)][PiP]
        nz=F.pw(u,q-1); zl=F.add[1][F.neg[F.pw(yl,q-1)]]
        lhs=F.s(s,tau,F.p(nz,F.pw(yl,q-2),PiP),F.neg[F.p(nz,zl,e1)])
        if lhs: bad1+=1
        r1=F.s(F.p(u,yl,e1), F.mul[F.s(F.mul[u][yl],u,yl)][PiP])
        if r1: bad2+=1
    print("n=%d q=%d |W|=%d : (O) fails at %d points ; (R1) fails at %d points"%(n,q,len(W),bad1,bad2), flush=True)
run(3,9); run(3,27); run(5,9)
