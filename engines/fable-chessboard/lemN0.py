# Lemma N0 (Fable 12): on W_(1,1)(n) (anchors s,s'), Q := (y minus {a,b}) u {s,s'}, sigma_M(x;Q) := sum_p x^{M-p} e_p(Q).
# (i) sigma_M(b;Q) = (-1)^M sigma_M(a;Q) on W for every M >= n+1  (checked on ALL points);
# (ii) after x^q -> x, the relation at M = n+q-1 has y-top form  s s' (B - eps A)  (degree q+n-3, eps = (-1)^n), rest of degree <= n;
#      the relation at M = n+q-2 has top form (s+s')(B + eps A) in degree q+n-3;  A = a^{q-1} x_{y-ab}, B = b^{q-1} x_{y-ab}.
import itertools, sys
from fq import Fq
from relab import red, top, show
from grepy_polys import add, mul, mono, e_
q=int(sys.argv[2]); n=int(sys.argv[1]); F=Fq(q); s,s2=1,3
W=[y for y in itertools.product(range(q),repeat=n) if F.is_closed(list(y)+[s,s2])]
def sig(x,Qv,M):
    r=0
    for p in range(0,min(M,len(Qv))+1): r=F.add[r][F.mul[F.pw(x,M-p)][F.esym(Qv,p)]]
    return r
bad=0; tot=0
for M in range(n+1,n+2*q+2):
    for y in W:
        Qv=list(y[2:])+[s,s2]; lhs=sig(y[1],Qv,M); rhs=sig(y[0],Qv,M)
        if M%2: rhs=F.neg[rhs]
        tot+=1; bad+= (lhs!=rhs)
print('(i) q=%d n=%d |W|=%d: relation sigma_M(b;Q) = (-1)^M sigma_M(a;Q), M = n+1..n+2q+1: %d/%d points*M OK'%(q,n,len(W),tot-bad,tot))
# (ii) symbolic: formal anchors s1 = s+s' (slot n), s2 = ss' (slot n+1); Q = P u {s,s'} => e_p(Q) = e_p(P) + s1 e_{p-1}(P) + s2 e_{p-2}(P)
nv=n+2; P=list(range(2,n))
def eQ(p): return add(add(e_(nv,P,p),mul(mono(nv,{n:1}),e_(nv,P,p-1))),mul(mono(nv,{n+1:1}),e_(nv,P,p-2)))
def sigS(x,M):
    R={}
    for p in range(0,min(M,n)+1): R=add(R,mul(mono(nv,{x:M-p}),eQ(p)))
    return R
for M in (n+q-1,n+q-2):
    rel=add(sigS(1,M),sigS(0,M),-((-1)**M))
    R=red(rel,q,n); d,T=top(R,n)
    sec=max([sum(m[:n]) for m in R if sum(m[:n])<d] or [-1])
    print('(ii) M=%d: top y-degree %d, form: %s ; next degree present: %d'%(M,d,show(T,n),sec))
