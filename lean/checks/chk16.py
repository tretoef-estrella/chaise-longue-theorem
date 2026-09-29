import itertools
from collections import Counter
def shape(xi,eta):
    X=Counter(xi); Y=Counter(eta); vals=set(X)|set(Y)
    lp=tuple(sorted([X[u]-Y[u] for u in vals if X[u]>Y[u]],reverse=True))
    lm=tuple(sorted([Y[u]-X[u] for u in vals if Y[u]>X[u]],reverse=True))
    return lp,lm
def S(t,l): return sum(l[:t])
def wd(a,b): return all(S(t,a)<=S(t,b) for t in range(1,max(len(a),len(b))+2))
def bwd(A,B): return wd(A[0],B[0]) and wd(A[1],B[1])
def subE(l,j): x=list(l); x[j-1]-=1; return tuple(sorted([v for v in x if v>0],reverse=True))
def addE(l,j): x=list(l); x[j-1]+=1; return tuple(sorted(x,reverse=True))
def addOne(l): return tuple(sorted(list(l)+[1],reverse=True))
def opt(mu,q,p):
    mp,mm=mu; lp,lm=len(mp),len(mm)
    if p<=lm: return (mp,subE(mm,p))
    if p<=q-lp: return (addOne(mp),mm)
    return (addE(mp,q+1-p),mm)
def parts(n):
    if n==0: yield (); return
    def g(n,m):
        if n==0: yield (); return
        for x in range(min(n,m),0,-1):
            for r in g(n-x,x): yield (x,)+r
    yield from g(n,n)
def BPar(q,a,b):
    out=[]
    for sp in range(0,a+b+1):
        for sm in range(0,a+b+1):
            if sp-sm!=a-b or sp+sm>a+b: continue
            for P in parts(sp):
                for M in parts(sm):
                    if len(P)+len(M)<=q: out.append((P,M))
    return out
bad=0;n=0
# (ii) fibre multiset = options multiset, (i) options in BPar
for q in (3,5):
  for a in range(1,4):
    for b in range(0,4):
      BP=set(BPar(q,a,b))
      for xi in itertools.product(range(q),repeat=a-1):
        for eta in itertools.product(range(q),repeat=b):
          mu=shape(xi,eta)
          fib=Counter(shape((u,)+xi,eta) for u in range(q))
          op=Counter(opt(mu,q,p) for p in range(1,q+1)); n+=1
          if fib!=op or any(o not in BP for o in op): bad+=1
print('fibre=options & options in BPar:',n,'tails, failures',bad)
# (iii) chain
bad=0;n=0
for q in (3,5,7):
  for a in range(0,5):
    for b in range(0,5):
      for mu in BPar(q,a,b):
        ops=[opt(mu,q,p) for p in range(1,q+1)]; n+=1
        if not all(bwd(ops[i],ops[i+1]) for i in range(q-1)): bad+=1
print('chain:',n,'shapes, failures',bad)
# (iv),(v) initial segment and three cases, all down-sets of BPar(q,a,b) small
def downsets(P):
    idx={p:i for i,p in enumerate(P)}; below=[[j for j,x in enumerate(P) if bwd(x,y)] for y in P]
    res=[]
    for mask in range(1<<len(P)):
        if all(all(mask>>j&1 for j in below[i]) for i in range(len(P)) if mask>>i&1): res.append(set(P[i] for i in range(len(P)) if mask>>i&1))
    return res
bad=0;n=0
for q,a,b in ((3,2,1),(3,1,2),(3,2,2),(5,2,1),(5,1,1),(3,3,1)):
    P=BPar(q,a,b); Ds=downsets(P); tails=BPar(q,a-1,b)
    for L in Ds:
        for mu in tails:
            mp,mm=mu; lp,lm=len(mp),len(mm)
            ins=[p for p in range(1,q+1) if opt(mu,q,p) in L]; Phi=len(ins); n+=1
            if ins!=list(range(1,Phi+1)): bad+=1; continue
            if Phi==0: continue
            if Phi>q-lp:
                j0=q+1-Phi; ok= opt(mu,q,Phi)==(addE(mp,j0),mm) and (j0==1 or mp[j0-2]>mp[j0-1])
            elif Phi>lm:
                ok= Phi==q-lp and opt(mu,q,Phi)==(addOne(mp),mm)
            else:
                r=Phi; ok= opt(mu,q,r)==(mp,subE(mm,r)) and (r==lm or mm[r]<mm[r-1])
            if not ok: bad+=1
print('initial segment & three cases:',n,'(down-set, tail) pairs, failures',bad)
