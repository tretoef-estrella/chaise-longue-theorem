# (1) profiles b: casilla HS F_n(b) (rank recursion = Theorem Gamma rows)  vs  t^{?} sum_lam mult m^b_lam(1/t)
# (2) extra cells q=11 n<=4
import itertools
exec(open('lusztig_B.py').read().split('data={}')[0])
src=open('regla_explicita.py').read().split('bad=0')[0]
exec(src.replace('def make(q)','def makeF(q)'))
def make_mb(m):
    PR=posroots(m); W=weyl(m); rho2=tuple(2*m-1-2*i for i in range(m))
    from functools import lru_cache
    @lru_cache(None)
    def P(gamma,k):
        if all(x==0 for x in gamma): return {0:1}
        if k==len(PR): return {}
        out={}; r=PR[k]; g=gamma; c=0
        while True:
            for d,v in P(g,k+1).items(): out[d+c]=out.get(d+c,0)+v
            g=tuple(a-b for a,b in zip(g,r)); c+=1
            if any(sum(g[:i+1])<0 for i in range(m)) or c>80: break
        return out
    def mb(lam,mu):
        res={}; lr2=tuple(2*a+b for a,b in zip(lam,rho2)); mr2=tuple(2*a+b for a,b in zip(mu,rho2))
        for w in W:
            v=act(w,lr2); gam2=tuple(a-b for a,b in zip(v,mr2))
            if any(x%2 for x in gam2): continue
            gam=tuple(x//2 for x in gam2)
            if any(sum(gam[:i+1])<0 for i in range(m)): continue
            for d,c in P(gam,0).items(): res[d]=res.get(d,0)+w[2]*c
        return {d:c for d,c in res.items() if c}
    return mb
ok=0;tot=0
for q,nmax in [(3,8),(5,6),(7,5)]:
    m=(q-1)//2; mb=make_mb(m); mF,N,F=makeF(q)
    for n in range(1,nmax+1):
        dec=tensor_decomp(m,n)
        for b in itertools.product(range(n,-1,-1),repeat=m):
            if any(b[i]<b[i+1] for i in range(m-1)): continue
            if N(n,b)==0: continue
            tot_={}
            for lam,c in dec.items():
                for d,v in mb(lam,b).items(): tot_[d]=tot_.get(d,0)+c*v
            Fb=list(F(n,b,'key'))
            # reverse with shift so that degree 0 matches
            tot_={d:v for d,v in tot_.items() if v}; D=max(tot_)
            rev=[tot_.get(D-d,0) for d in range(D+1)]
            while rev and rev[-1]==0: rev.pop()
            tot+=1; good= rev==Fb; ok+=good
            if not good: print('NO',q,n,b,'lus',rev,'F',Fb, 'maxdeg',D,'mn-|b|',m*n-sum(b))
print('profiles (dominant b) matching',ok,'of',tot)
