import sys, numpy as np, time
from fdeg12 import Space, fibre
from fq import Fq
q=9; F=Fq(q); n=int(sys.argv[1]); T0=time.time()
W=fibre(q,n,[1,3]); S=Space(q,W); print('|W|=',len(W))
a,b,c,d=0,1,2,3; C=list(range(4,n)); f=n-2
pw=F.pw; ml=F.mul; ad=F.add
def e(vals,k): return F.esym(vals,k)
def u(x): return 1 if x==0 else 0
def vec(fn): return np.array([fn(y) for y in W],dtype=np.int64)
def prod(vals):
    r=1
    for x in vals: r=ml[r][x]
    return r
def neg(x): return F.neg[x]
tests={
 'F2 = (ab)^7 e_{f-1}(y-cd)  deg %d'%(2*q+f-5): lambda y: ml[pw(ml[y[a]][y[b]],q-2)][e([y[i] for i in range(n) if i not in (c,d)],f-1)],
 'phi_ab = a^7 e_f(y-b) deg %d'%(q+f-2): lambda y: ml[pw(y[a],q-2)][e([y[i] for i in range(n) if i!=b],f)],
 'D_a;cd = a^7 e_{f-1}(y-cd) deg %d'%(q+f-3): lambda y: ml[pw(y[a],q-2)][e([y[i] for i in range(n) if i not in (c,d)],f-1)],
 'c*D deg %d'%(q+f-2): lambda y: ml[y[c]][ml[pw(y[a],q-2)][e([y[i] for i in range(n) if i not in (c,d)],f-1)]],
 'u_a*b^7 x_C deg %d'%(2*q+f-5): lambda y: ml[u(y[a])][ml[pw(y[b],q-2)][prod([y[i] for i in C])]],
 'u_a*xi(b) deg %d'%(2*q+f-5): lambda y: ml[u(y[a])][ad[ad[ml[pw(y[b],q-2)][prod([y[i] for i in C])]][ml[pw(y[b],q-1)][e([y[i] for i in C],len(C)-1)]]][neg(e([y[i] for i in C],len(C)-1))]],
 'u_a u_b e_{|C|-1}(C) deg %d'%(2*q+f-5): lambda y: ml[u(y[a])*u(y[b])][e([y[i] for i in C],len(C)-1)],
 'a^8 x_{y-ab} (N0,|A|=1) deg %d'%(q-1+n-2): lambda y: ml[pw(y[a],q-1)][prod([y[i] for i in range(n) if i not in (a,b)])],
}
for k,fn in tests.items():
    v=vec(fn); dg=int(k.split('deg ')[1])
    fd=S.fdeg(v,dg)
    print('%-40s fdeg = %s  %s   [%.1fs]'%(k,fd,'(IN gr I)' if fd is not None and fd<dg else '(not lowered)',time.time()-T0),flush=True)
