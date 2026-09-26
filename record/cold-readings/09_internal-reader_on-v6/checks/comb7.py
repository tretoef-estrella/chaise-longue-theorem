import itertools
from collections import Counter
def parts(n,maxpart=None):
    if maxpart is None: maxpart=n
    if n==0: yield (); return
    for k in range(min(n,maxpart),0,-1):
        for r in parts(n-k,k): yield (k,)+r
def S(l,t): return sum(sorted(l,reverse=True)[:t])
def dom(a,b):
    L=max(len(a),len(b))+1
    return all(S(a,t)<=S(b,t) for t in range(1,L+1))
def bdom(A,B): return dom(A[0],B[0]) and dom(A[1],B[1])
def BPar(q,al,be):
    out=[]
    for sp in range(0,al+be+1):
        # |l+|-|l-|=al-be, |l+|+|l-|=sp
        if (sp+al-be)%2: continue
        np_=(sp+al-be)//2; nm=sp-np_
        if np_<0 or nm<0: continue
        for lp in parts(np_):
            for lm in parts(nm):
                if len(lp)+len(lm)<=q: out.append((lp,lm))
    return out
def srt(l): return tuple(sorted([x for x in l if x>0],reverse=True))
def opts(mu,q):
    mp,mm=mu; lp,lm=len(mp),len(mm); o=[]
    for p in range(1,q+1):
        if p<=lm:
            l=list(mm); l[p-1]-=1; o.append((mp,srt(l)))
        elif p<=q-lp: o.append((srt(mp+(1,)),mm))
        else:
            j=q+1-p; l=list(mp); l[j-1]+=1; o.append((srt(l),mm))
    return o
def shape(xi,eta):
    X=Counter(xi);Y=Counter(eta)
    return (srt([X[u]-Y[u] for u in X if X[u]>Y[u]]), srt([Y[u]-X[u] for u in Y if Y[u]>X[u]]))
bad=0;pairs=0
for q in [3,5,7,9]:
  for al in range(1,7):
    for be in range(0,7):
        if al+be>9: continue
        tails=BPar(q,al-1,be); full=set(BPar(q,al,be))
        for mu in tails:
            o=opts(mu,q)
            assert all(x in full for x in o)
            if not all(bdom(o[i],o[i+1]) for i in range(q-1)): bad+=1; print("chain",q,al,be,mu)
        for mu in tails:
            for mt in tails:
                if mu!=mt and bdom(mu,mt):
                    pairs+=1
                    o1=opts(mu,q);o2=opts(mt,q)
                    for p in range(q):
                        if not bdom(o1[p],o2[p]): bad+=1; print("P2",q,al,be,mu,mt,p+1)
print("prop7.4 bad",bad,"pairs",pairs)
# P1 brute force: fibre size equals F_Lambda for random downsets -> check opt mapping directly
import random
bad=0;tests=0
for q in [3,5]:
  for al,be in [(2,1),(2,2),(3,2),(3,3)]:
    Om=range(q)
    for tail in itertools.product(Om,repeat=al-1+be):
        xi=tail[:al-1]; eta=tail[al-1:]
        mu=shape(xi,eta); o=opts(mu,q)
        got=Counter(shape((u,)+xi,eta) for u in Om)
        tests+=1
        if got!=Counter(o): bad+=1
print("P1 bad",bad,"tests",tests)
