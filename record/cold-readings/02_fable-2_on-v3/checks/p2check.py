"""Independent check of Proposition 5.6 (P2), Lemma 5.5 (chain) and formula (5.1)/(P1) at large h.
All from the definitions in 5.2-5.5 (no use of the paper's case analysis).
Par_m := {lambda : |lambda|<=m, |lambda| = m mod 2, l(lambda) <= h}.  opt_p as in 5.5."""
import sys, itertools
def partitions_upto(maxsize, maxlen):
    out=[()]
    def rec(cur, rem, maxpart):
        for p in range(min(rem,maxpart),0,-1):
            if len(cur)+1>maxlen: return
            nxt=cur+(p,)
            out.append(nxt)
            rec(nxt, rem-p, p)
    rec((), maxsize, maxsize)
    return out
def S(lam,t): return sum(lam[:t])
def leq(lam,mu):   # weak dominance lam <= mu
    T=max(len(lam),len(mu))+1
    return all(S(lam,t)<=S(mu,t) for t in range(1,T+1))
def norm(l): return tuple(sorted([x for x in l if x>0], reverse=True))
def options(mu,q):
    L=q-1; l=len(mu)
    opts=[]
    for p in range(1,l+1): opts.append(norm(mu[:p-1]+(mu[p-1]-1,)+mu[p:]))
    for p in range(l+1, L-l+1): opts.append(norm(mu+(1,)))
    for j in range(l,0,-1): opts.append(norm(mu[:j-1]+(mu[j-1]+1,)+mu[j:]))
    assert len(opts)==L
    return opts
def check(q, m):
    h=(q-1)//2
    Par=[lam for lam in partitions_upto(m-1, h) if (sum(lam)-(m-1))%2==0]
    fails=0; pairs=0
    # chain (Lemma 5.5) for every mu in Par_{m-1}
    for mu in Par:
        o=options(mu,q)
        for p in range(len(o)-1):
            if not leq(o[p],o[p+1]): print("CHAIN FAIL",q,m,mu,p); fails+=1
    # P2: mu <= mut  => opt_p(mu) <= opt_p(mut) for all p
    opt={mu:options(mu,q) for mu in Par}
    for mu in Par:
        for mut in Par:
            if mu==mut or not leq(mu,mut): continue
            pairs+=1
            for p in range(q-1):
                if not leq(opt[mu][p],opt[mut][p]):
                    print("P2 FAIL",q,m,mu,mut,"position",p+1,opt[mu][p],opt[mut][p]); fails+=1
    print(f"q={q} m={m}: |Par_{m-1}|={len(Par)} comparable pairs={pairs} failures={fails}", flush=True)
    return fails
if __name__=="__main__":
    tot=0
    for q,ms in [(27,[3,4,5,6,7,8,9,10]),(81,[4,6,8,9]),(9,[5,7,9,11,13]),(3,[5,9,13])]:
        for m in ms: tot+=check(q,m)
    print("TOTAL FAILURES", tot)
