# INFORME_7 STEP 1.1: descent test at k=2, q=9 (and 27) on W_0 = V'_1 = perm(-1,0,c,-c):
# is s0 = x1^(q-2) e_2(x1,x2,x3)  (= x_j^(q-2) e_{2k-2}(V), l=0, j=1)  in  span{t_b = x1^(q-1) x_{C_b}} + F_{q-1}(W_0) ?
# and the same for s0' = x0^2 x1^(q-2) (G-a).  F_d(W_0) = functions of polynomial degree <= d.
import sys, itertools
from fq import Fq
def monos(n,d):
    out=[]
    for e in itertools.product(range(d+1),repeat=n):
        if sum(e)<=d: out.append(e)
    return out
def rank_and_membership(F, rows_basis, targets):
    # Gaussian elimination over F_q on columns = points. rows_basis: list of vectors; targets: list of vectors.
    # returns rank of basis and, for each target, whether it lies in the span.
    q=F.q; piv={}  # pivot col -> row
    def reduce(vec):
        vec=list(vec)
        for c in range(len(vec)):
            if vec[c]!=0 and c in piv:
                r=piv[c]; f=vec[c]
                for j in range(len(vec)):
                    if r[j]: vec[j]=F.add[vec[j]][F.neg[F.mul[f][r[j]]]]
        return vec
    for v in rows_basis:
        v=reduce(v)
        for c in range(len(v)):
            if v[c]!=0:
                inv=F.inv[v[c]]; v=[F.mul[inv][x] for x in v]; piv[c]=v; break
    res=[]
    for t in targets:
        r=reduce(t); res.append(all(x==0 for x in r))
    return len(piv), res
for q in [9,27]:
    F=Fq(q); k=2; n=2*k
    W=F.W0(k)
    ev=lambda f: [f(y) for y in W]
    x=lambda i: (lambda y: y[i])
    def mono(e): return lambda y: F.p(*[F.pw(y[i],e[i]) for i in range(n)])
    low=[ev(mono(e)) for e in monos(n,q-1)]
    e2V=lambda y: F.esym([y[1],y[2],y[3]],2)
    s0=ev(lambda y: F.mul[F.pw(y[1],q-2)][e2V(y)])
    s0p=ev(lambda y: F.mul[F.pw(y[0],2)][F.pw(y[1],q-2)])
    tb={}
    for b in [0,2,3]:
        C=[i for i in range(n) if i not in (1,b)]
        tb[b]=ev(lambda y,C=C: F.mul[F.pw(y[1],q-1)][F.p(*[y[i] for i in C])])
    r0,m=rank_and_membership(F, low, [s0,s0p])
    print("q=%d dim F_{q-1}(W_0)=%d ; s0 in F_{q-1}: %s ; x0^2x1^(q-2) in F_{q-1}: %s"%(q,r0,m[0],m[1]))
    r1,m=rank_and_membership(F, low+list(tb.values()), [s0,s0p])
    print("   with the 3 t_b added: rank %d ; s0 in span: %s ; x0^2x1^(q-2): %s"%(r1,m[0],m[1]))
    # which combination? try each single t_b and pairs
    for b in tb:
        r,m=rank_and_membership(F, low+[tb[b]], [s0,s0p]); print("   t_%d alone: s0 %s, s0' %s"%(b,m[0],m[1]))
