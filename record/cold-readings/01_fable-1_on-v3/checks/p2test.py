# Independent test of Proposition 5.6 (P2), Lemma 5.5 (chain) and formula (5.1) of the paper.
# Enumerates ALL pairs mu <= mutilde (weak dominance) in Par_{m-1} and checks opt_p(mu) <= opt_p(mutilde) for every position p.
import itertools, sys

def partitions_upto(maxsize, maxlen):
    res=[]
    def rec(rem, maxpart, cur):
        res.append(tuple(cur))
        if len(cur)>=maxlen: return
        for part in range(min(rem,maxpart),0,-1):
            rec(rem-part, part, cur+[part])
    rec(maxsize, maxsize, [])
    return res

def S(lam,t):
    return sum(lam[:t])

def leq(lam,mu):
    T=max(len(lam),len(mu))+1
    return all(S(lam,t)<=S(mu,t) for t in range(1,T+1))

def sort_desc(l):
    return tuple(sorted([x for x in l if x>0],reverse=True))

def options(mu,q):
    h=(q-1)//2; L=q-1; l=len(mu)
    opts=[]
    for pidx in range(l):           # removals mu - e_p, p=1..l
        v=list(mu); v[pidx]-=1; opts.append(sort_desc(v))
    for _ in range(L-2*l):          # middle: mu ⊔ 1
        opts.append(sort_desc(list(mu)+[1]))
    for j in range(l,0,-1):         # additions mu + e_j at position L+1-j, i.e. j = l, ..., 1
        v=list(mu); v[j-1]+=1; opts.append(sort_desc(v))
    assert len(opts)==L
    return opts

def run(q, m):
    h=(q-1)//2
    Par=[lam for lam in partitions_upto(m-1,h) if (sum(lam)-(m-1))%2==0]
    # Lemma 5.5 chain
    for mu in Par:
        o=options(mu,q)
        for a,b in zip(o,o[1:]):
            assert leq(a,b), ("chain fails",q,m,mu,a,b)
        # all options in Par_m
        for x in o:
            assert sum(x)<=m and (sum(x)-m)%2==0 and len(x)<=h, ("option outside Par_m",mu,x)
    # P2
    pairs=0; fails=[]
    for mu in Par:
        omu=options(mu,q)
        for mt in Par:
            if not leq(mu,mt): continue
            pairs+=1
            omt=options(mt,q)
            for p,(a,b) in enumerate(zip(omu,omt),1):
                if not leq(a,b):
                    fails.append((mu,mt,p,a,b))
    return len(Par),pairs,fails

if __name__=="__main__":
    for q,m in [(3,4),(3,6),(3,9),(3,13),(3,16),(9,4),(9,6),(9,8),(9,10),(9,12),(9,14),(27,6),(27,8),(27,10),(81,8)]:
        n,pairs,fails=run(q,m)
        print(f"q={q} m={m}: |Par_(m-1)|={n}, comparable pairs={pairs}, P2 failures={len(fails)}")
        for f in fails[:5]: print("   ",f)
