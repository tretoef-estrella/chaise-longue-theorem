import itertools, sys
exec(open('chk16.py').read().split('bad=0;n=0')[0])
def downsets(P):
    below=[[j for j,x in enumerate(P) if bwd(x,y)] for y in P]
    res=[]
    for mask in range(1<<len(P)):
        if all(all(mask>>j&1 for j in below[i]) for i in range(len(P)) if mask>>i&1):
            res.append(set(P[i] for i in range(len(P)) if mask>>i&1))
    return res
def colLen(l,c): return sum(1 for v in l if v>=c)
def set_partitions_sizes(items,sizes):
    # ordered blocks with given sizes
    if not sizes: 
        if not items: yield []
        return
    for comb in itertools.combinations(items,sizes[0]):
        rest=[x for x in items if x not in comb]
        for r in set_partitions_sizes(rest,sizes[1:]): yield [list(comb)]+r
def tight_patterns(lam,a,b):
    lp,lm=lam; np_=a-sum(lp)
    if np_<0 or b-sum(lm)!=np_: return
    for I in itertools.combinations(range(a),np_):
        for L in itertools.permutations(range(b),np_):
            restX=[i for i in range(a) if i not in I]; restZ=[l for l in range(b) if l not in L]
            sx=[colLen(lp,c) for c in range(1,(lp[0] if lp else 0)+1)]
            sz=[colLen(lm,c) for c in range(1,(lm[0] if lm else 0)+1)]
            for BX in set_partitions_sizes(restX,sx):
                for BZ in set_partitions_sizes(restZ,sz):
                    yield list(zip(I,L)),BX,BZ
def pmul(f,g,q,p):
    h={}
    for e1,c1 in f.items():
        for e2,c2 in g.items():
            e=tuple(x+y for x,y in zip(e1,e2))
            if e and max(e)>=q: continue
            h[e]=(h.get(e,0)+c1*c2)%p
    return {e:c for e,c in h.items() if c}
def var(k,n): return {tuple(1 if t==k else 0 for t in range(n)):1}
def lin(k1,k2,n,p): # y_k1 - y_k2
    return {tuple(1 if t==k1 else 0 for t in range(n)):1, tuple(1 if t==k2 else 0 for t in range(n)):p-1}
def product(pat,a,b,q,p):
    n=a+b; one={tuple([0]*n):1}; f=one
    P,BX,BZ=pat
    for (i,l) in P:
        d=lin(i,a+l,n,p); g=one
        for _ in range(q-1): g=pmul(g,d,q,p)
        f=pmul(f,g,q,p)
    for B in BX:
        B=sorted(B)
        for s in range(len(B)):
            for t in range(s+1,len(B)): f=pmul(f,lin(B[t],B[s],n,p),q,p)
    for B in BZ:
        B=sorted(B)
        for s in range(len(B)):
            for t in range(s+1,len(B)): f=pmul(f,lin(a+B[t],a+B[s],n,p),q,p)
    return f
def rref(rows,ncol,p):
    rows=[r[:] for r in rows]; piv=[]; R=[]
    for r in rows:
        for (pc,pr) in zip(piv,R):
            if r[pc]:
                c=r[pc]; r=[(x-c*y)%p for x,y in zip(r,pr)]
        nz=next((k for k in range(ncol) if r[k]),None)
        if nz is None: continue
        inv=pow(r[nz],p-2,p); r=[(x*inv)%p for x in r]
        for idx in range(len(R)):
            if R[idx][nz]:
                c=R[idx][nz]; R[idx]=[(x-c*y)%p for x,y in zip(R[idx],r)]
        piv.append(nz); R.append(r)
    return piv,R
def in_span(v,piv,R,p):
    v=v[:]
    for pc,pr in zip(piv,R):
        if v[pc]:
            c=v[pc]; v=[(x-c*y)%p for x,y in zip(v,pr)]
    return not any(v)
def run(q,a,b,p,shift=0,maxds=None):
    n=a+b; mons=list(itertools.product(range(q),repeat=n))
    # order: w-degree (first coord) descending
    mons.sort(key=lambda e:(-e[0],e))
    col={e:k for k,e in enumerate(mons)}; N=len(mons)
    tails=list(itertools.product(range(q),repeat=n-1)); tcol={e:k for k,e in enumerate(tails)}
    BP=BPar(q,a,b); Ds=downsets(BP)
    if maxds: Ds=Ds[:maxds]
    prodcache={}
    def prods(lam,aa,bb):
        key=(lam,aa,bb)
        if key not in prodcache: prodcache[key]=[product(t,aa,bb,q,p) for t in tight_patterns(lam,aa,bb)]
        return prodcache[key]
    ninc=0; bad=0
    for L in Ds:
        if not L: continue
        rows=[]
        for lam in L:
            for G in prods(lam,a,b):
                for m in mons:
                    h=pmul({m:1},G,q,p)
                    if h:
                        v=[0]*N
                        for e,c in h.items(): v[col[e]]=c
                        rows.append(v)
        piv,R=rref(rows,N,p)
        for i in range(q):
            j=q-1-i-shift
            layer=[mu for mu in BPar(q,a-1,b) if sum(1 for pp in range(1,q+1) if opt(mu,q,pp) in L)>i]
            gens=[G for mu in layer for G in prods(mu,a-1,b)]
            if not gens: continue
            ninc+=1
            if j<0: bad+=1; continue
            Wrows=[]
            for pc,r in zip(piv,R):
                if mons[pc][0]<=j:
                    v=[0]*len(tails)
                    for k,c in enumerate(r):
                        if c and mons[k][0]==j: v[tcol[mons[k][1:]]]=c
                    Wrows.append(v)
            wp,WR=rref(Wrows,len(tails),p)
            ok=True
            for G in gens:
                v=[0]*len(tails)
                for e,c in G.items(): v[tcol[e]]=c
                if not in_span(v,wp,WR,p): ok=False;break
            if not ok: bad+=1
    return len(Ds),ninc,bad
cells=[(3,1,1,3),(3,2,1,3),(3,1,2,3),(3,2,2,3),(3,3,1,3),(3,1,3,3),(5,1,1,5),(5,2,1,5),(5,1,2,5),(7,1,1,7),(7,2,1,7),(3,2,2,101),(5,2,1,101)]
tot=0;totbad=0
for q,a,b,p in cells:
    d,ni,bd=run(q,a,b,p); tot+=ni; totbad+=bd
    print('q=%d a=%d b=%d p=%d: downsets %d, inclusions %d, failures %d'%(q,a,b,p,d,ni,bd)); sys.stdout.flush()
print('TOTAL inclusions',tot,'failures',totbad)
negtot=0;negbad=0
for q,a,b,p in [(3,2,1,3),(3,2,2,3),(5,2,1,5),(3,1,2,3)]:
    d,ni,bd=run(q,a,b,p,shift=1); negtot+=ni; negbad+=bd
    print('NEG slice-1 q=%d a=%d b=%d: inclusions %d, failures %d'%(q,a,b,ni,bd))
print('NEG total',negtot,'failures',negbad)
for q,a,b,p in [(7,1,1,5),(7,1,2,5),(7,2,1,5)]:
    d,ni,bd=run(q,a,b,p)
    print('FIELD control q=7 over F_5 (C(6,2)=0) a=%d b=%d: inclusions %d, failures %d'%(a,b,ni,bd))
