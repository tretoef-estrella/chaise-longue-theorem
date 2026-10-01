# Type C_m test: HS of QQ[x]/(e_odd, x^{2m}) (n even) vs t^{D} sum mult m^0_lam(1/t), Sp(2m), V=C^{2m}
import itertools
from functools import lru_cache
def posroots(m):
    R=[]
    for i in range(m):
        for j in range(i+1,m):
            v=[0]*m; v[i]=1; v[j]=-1; R.append(tuple(v)); v=[0]*m; v[i]=1; v[j]=1; R.append(tuple(v))
        v=[0]*m; v[i]=2; R.append(tuple(v))
    return R
def weyl(m):
    W=[]
    for perm in itertools.permutations(range(m)):
        sg=1
        for i in range(m):
            for j in range(i+1,m):
                if perm[i]>perm[j]: sg=-sg
        for signs in itertools.product((1,-1),repeat=m):
            W.append((perm,signs,sg*(-1)**signs.count(-1)))
    return W
def act(w,v): return tuple(w[1][i]*v[w[0][i]] for i in range(len(v)))
def make(m):
    PR=posroots(m); W=weyl(m); rho=tuple(m-i for i in range(m))
    @lru_cache(None)
    def P(g,k):
        if all(x==0 for x in g): return {0:1}
        if k==len(PR): return {}
        out={}; r=PR[k]; c=0
        while True:
            for d,v in P(g,k+1).items(): out[d+c]=out.get(d+c,0)+v
            g=tuple(a-b for a,b in zip(g,r)); c+=1
            if any(sum(g[:i+1])<0 for i in range(m)) or c>80: break
        return out
    def m0(lam):
        res={}; lr=tuple(a+b for a,b in zip(lam,rho))
        for w in W:
            gam=tuple(a-b for a,b in zip(act(w,lr),rho))
            if any(sum(gam[:i+1])<0 for i in range(m)): continue
            for d,c in P(gam,0).items(): res[d]=res.get(d,0)+w[2]*c
        return {d:c for d,c in res.items() if c}
    return m0
def dec(m,n):
    cur={tuple([0]*m):1}
    for _ in range(n):
        nx={}
        for lam,c in cur.items():
            for i in range(m):
                for s in (1,-1):
                    v=list(lam); v[i]+=s
                    if all(v[k]>=v[k+1] for k in range(m-1)) and v[-1]>=0: nx[tuple(v)]=nx.get(tuple(v),0)+c
        cur=nx
    return cur
import re
for line in open('tipoC.log'):
    mm=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\}',line)
    if not mm: continue
    q,n=int(mm[1]),int(mm[2]); hf=[int(x) for x in mm[3].split(',')]
    if n%2: continue
    m=q//2; m0=make(m); tot={}
    for lam,c in dec(m,n).items():
        for d,v in m0(lam).items(): tot[d]=tot.get(d,0)+c*v
    tot={d:v for d,v in tot.items() if v}; D=max(tot)
    rev=[tot.get(D-d,0) for d in range(D+1)]
    while rev and rev[-1]==0: rev.pop()
    print(q,n,'lusztigC rev',rev,'HF',hf,'MATCH' if rev==hf else 'NO','D=',D,'(q-1)n/2=',(q-1)*n/2)
