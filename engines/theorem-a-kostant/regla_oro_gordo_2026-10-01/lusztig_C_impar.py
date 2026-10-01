exec(open('lusztig_C.py').read().split('import re')[0])
import re
from functools import lru_cache
def make_mu(m):
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
    def mmu(lam,mu):
        res={}; lr=tuple(a+b for a,b in zip(lam,rho)); mr=tuple(a+b for a,b in zip(mu,rho))
        for w in W:
            gam=tuple(a-b for a,b in zip(act(w,lr),mr))
            if any(sum(gam[:i+1])<0 for i in range(m)): continue
            for d,c in P(gam,0).items(): res[d]=res.get(d,0)+w[2]*c
        return {d:c for d,c in res.items() if c}
    return mmu
for line in open('impares.txt'):
    mm=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\}',line); q,n=int(mm[1]),int(mm[2]); hf=[int(x) for x in mm[3].split(',')]
    m=q//2; mu=tuple([1]+[0]*(m-1)); f=make_mu(m); tot={}
    for lam,c in dec(m,n).items():
        for d,v in f(lam,mu).items(): tot[d]=tot.get(d,0)+c*v
    tot={d:v for d,v in tot.items() if v}; D=max(tot)
    rev=[tot.get(D-d,0) for d in range(D+1)]
    while rev and rev[-1]==0: rev.pop()
    print(q,n,'weight e1 lusztig rev',rev,'HF',hf,'MATCH' if rev==hf else 'NO', 'sumHF',sum(hf))
