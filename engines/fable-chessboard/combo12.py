# combo12.py — Fable 12: search a combination of the "boson" relations  sum_p e_p(Z\X) c^X_{M-p} = 0 (M > |Z\X|),
# c^X(t) = prod_{x in X}(1+xt)/(1-xt), X = {c,d} u T, T subset of {a,b,s,s'}, whose reduced (x^q->x) top form is F2_{ab;cd}.
# Arithmetic over GF(9) (anchors s = 1, s' = 3 in fq encoding), (1,1), n given.
import sys, itertools, numpy as np, time
from fq import Fq
q=9; F=Fq(q); n=int(sys.argv[1]); f=n-2; T0=time.time()
s,s2=1,3; a,b,c,d=0,1,2,3; C=list(range(4,n)); target_deg=2*q+f-5
AD=F.add; ML=F.mul
def padd(P,Q,k=1):
    R=dict(P)
    for m,v in Q.items():
        w=AD[R.get(m,0)][ML[k][v]]
        if w: R[m]=w
        elif m in R: del R[m]
    return R
def pmul(P,Q):
    R={}
    for m1,v1 in P.items():
        for m2,v2 in Q.items():
            m=tuple(x+y for x,y in zip(m1,m2)); w=AD[R.get(m,0)][ML[v1][v2]]
            if w: R[m]=w
            elif m in R: del R[m]
    return R
def red(P):
    R={}
    for m,v in P.items():
        m=list(m)
        for i in range(n):
            while m[i]>=q: m[i]-=q-1
        m=tuple(m); w=AD[R.get(m,0)][v]
        if w: R[m]=w
        elif m in R: del R[m]
    return R
one=tuple([0]*n)
def var(i): e=[0]*n; e[i]=1; return {tuple(e):1}
def const(k): return {one:k} if k else {}
def lin(x,sign):   # 1 + sign*x t  as list of coefficients (poly in y) : x is ('v',i) or ('k',field)
    return x
# element objects: letters as polys, anchors as constants
def elem(x): return var(x) if isinstance(x,int) else const(x[1])
def series_coeffs(X,K):   # coefficients c_0..c_K of prod_{x in X} (1+xt)/(1-xt)
    ser=[const(1)]+[{} for _ in range(K)]
    for x in X:
        ex=elem(x)
        # (1+xt)/(1-xt) = 1 + 2 sum_{m>=1} x^m t^m
        pw=[const(1)]
        for m in range(1,K+1): pw.append(pmul(pw[-1],ex))
        fac=[const(1)]+[ {mm:ML[2][v] for mm,v in pw[m].items()} for m in range(1,K+1)]
        new=[{} for _ in range(K+1)]
        for i in range(K+1):
            if not ser[i]: continue
            for j in range(K+1-i):
                new[i+j]=padd(new[i+j],pmul(ser[i],fac[j]))
        ser=[red(p) for p in new]
    return ser
def esym(elems,k):
    E=[const(1)]+[{} for _ in elems]
    for x in elems:
        ex=elem(x)
        for dd in range(len(elems),0,-1): E[dd]=padd(E[dd],pmul(E[dd-1],ex))
    return E[k] if 0<=k<=len(elems) else {}
Zall=list(range(n))+[('k',s),('k',s2)]
rels={}
for T in itertools.chain.from_iterable(itertools.combinations([a,b,('k',s),('k',s2)],r) for r in range(5)):
    X=[c,d]+list(T); ZX=[z for z in Zall if z not in X]
    Kmax=2*q+6; ser=series_coeffs(X,Kmax+len(ZX)+1); es=[esym(ZX,p) for p in range(len(ZX)+1)]
    for M in range(len(ZX)+1, len(ZX)+Kmax):
        R={}
        for p in range(len(ZX)+1):
            if M-p<len(ser): R=padd(R,pmul(es[p],ser[M-p]))
        R=red(R)
        if R: rels[(tuple(str(t) for t in T),M)]=R
print('relations',len(rels),' [%.1fs]'%(time.time()-T0),flush=True)
# F2 target
Y=[i for i in range(n) if i not in (c,d)]
F2=red(pmul({tuple((q-2) if i in (a,b) else 0 for i in range(n)):1},esym(Y,f-1)))
# linear algebra: rows = monomials of degree >= target_deg, find sum c_i rel_i (restricted) == F2
mons=sorted({m for R in rels.values() for m in R if sum(m)>=target_deg}|set(F2))
idx={m:i for i,m in enumerate(mons)}
print('high monomials',len(mons),flush=True)
from ansatz12 import Solver
S=Solver(F,len(mons))
def vecof(R):
    v=np.zeros(len(mons),dtype=np.int64)
    for m,x in R.items():
        if sum(m)>=target_deg: v[idx[m]]=x
    return v
for k,R in rels.items(): S.add(vecof(R),k)
ok,cb=S.solve(vecof(F2))
print('F2 = top of a combination of boson relations:',ok,' rank',len(S.piv),' [%.1fs]'%(time.time()-T0))
if ok:
    for k,x in sorted(cb.items(),key=str): print('  ',x,k)
