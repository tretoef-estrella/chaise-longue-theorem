# Test: X_n(t) for q=2m+1  vs  sum_lambda mult_lambda(V^{(x)n}) * m^0_lambda(t)  (Lusztig q-analogue, type B_m)
import itertools, sys
from functools import lru_cache
from fractions import Fraction
def posroots(m):
    R=[]
    for i in range(m):
        for j in range(i+1,m):
            v=[0]*m; v[i]=1; v[j]=-1; R.append(tuple(v))
            v=[0]*m; v[i]=1; v[j]=1; R.append(tuple(v))
        v=[0]*m; v[i]=1; R.append(tuple(v))
    return R
def weyl(m):
    W=[]
    for perm in itertools.permutations(range(m)):
        # sign of perm
        sg=1; p=list(perm)
        for i in range(m):
            for j in range(i+1,m):
                if p[i]>p[j]: sg=-sg
        for signs in itertools.product((1,-1),repeat=m):
            s2=sg
            for x in signs:
                if x==-1: s2=-s2
            W.append((perm,signs,s2))
    return W
def act(w,v):
    perm,signs,_=w
    return tuple(signs[i]*v[perm[i]] for i in range(len(v)))
def make(m):
    PR=posroots(m); W=weyl(m)
    rho2=tuple(2*m-1-2*i for i in range(m))   # 2*rho
    @lru_cache(None)
    def P(gamma,k):  # t-Kostant partition: dict power->count, using roots PR[k:]
        if all(x==0 for x in gamma): return {0:1}
        if k==len(PR): return {}
        out={}
        r=PR[k]; g=gamma; c=0
        while True:
            sub=P(g,k+1)
            for d,v in sub.items(): out[d+c]=out.get(d+c,0)+v
            g=tuple(a-b for a,b in zip(g,r)); c+=1
            # stop if impossible: first nonzero coordinate partial sums
            if sum(x for x in g)< -100 or any(sum(g[:i+1])<-0 for i in range(m)) and False: break
            if c>60: break
            # feasibility: positive roots have nonneg partial sums of coords
            if any(sum(g[:i+1])<0 for i in range(m)): break
        return out
    def m0(lam):
        res={}
        lr2=tuple(2*a+b for a,b in zip(lam,rho2))
        for w in W:
            v=act(w,lr2)
            gam2=tuple(a-b for a,b in zip(v,rho2))
            if any(x%2 for x in gam2): continue
            gam=tuple(x//2 for x in gam2)
            if any(sum(gam[:i+1])<0 for i in range(m)): continue
            for d,c in P(gam,0).items(): res[d]=res.get(d,0)+w[2]*c
        return {d:c for d,c in res.items() if c}
    return m0
def tensor_decomp(m,n):
    cur={tuple([0]*m):1}
    for _ in range(n):
        nxt={}
        for lam,c in cur.items():
            outs=[]
            for i in range(m):
                for s in (1,-1):
                    v=list(lam); v[i]+=s
                    if all(v[k]>=v[k+1] for k in range(m-1)) and v[-1]>=0: outs.append(tuple(v))
            if lam[-1]>0: outs.append(lam)
            for o in outs: nxt[o]=nxt.get(o,0)+c
        cur=nxt
    return cur
data={}
for line in [l for l in open("hf_ext.log") if l.startswith("q=")]:
    pp=line.split(); q=int(pp[0][2:]); n=int(pp[1][2:])
    data[(q,n)]=[int(x) for x in line.split('{')[1].split('}')[0].split(',')]
for (q,n),hf in sorted(data.items()):
    m=(q-1)//2
    if m>6: continue
    m0=make(m); dec=tensor_decomp(m,n)
    tot={}
    for lam,c in dec.items():
        for d,v in m0(lam).items(): tot[d]=tot.get(d,0)+c*v
    L=max(tot)+1
    poly=[tot.get(d,0) for d in range(L)]
    N=m*n
    rev=[tot.get(N-d,0) for d in range(N+1)]
    while rev and rev[-1]==0: rev.pop()
    print(q,n,'sum m0=',poly,' X=',hf,' direct' if poly==hf else '', ' reversed(mn)' if rev==hf else '')
