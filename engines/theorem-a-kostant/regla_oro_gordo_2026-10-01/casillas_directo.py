# Direct check: Hilbert function of gr I(W_b(n)), W_b(n) = walks of length n ending at b,
# as a point set in F_p^n (values 0, +-g^j), against the fibre-rank recursion F_n(b).
import itertools, sys
exec(open('regla_explicita.py').read().split('bad=0')[0])
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def rankmod(rows,p):
    # incremental elimination; rows: list of lists
    piv={}; r=0
    for row in rows:
        row=row[:]
        for c,pr in piv.items():
            if row[c]:
                f=row[c]
                row=[(a-f*b)%p for a,b in zip(row,pr)]
        nz=next((i for i,a in enumerate(row) if a),None)
        if nz is None: continue
        inv=pow(row[nz],p-2,p); row=[a*inv%p for a in row]
        piv[nz]=row; r+=1
    return r
def gr_hf(q,n,b):
    m=(q-1)//2
    p=next(x for x in range(10007,20000) if isprime(x) and (x-1)%(q-1)==0)
    # element of order q-1
    g=next(x for x in range(2,p) if pow(x,q-1,p)==1 and all(pow(x,d,p)!=1 for d in range(1,q-1)))
    val={None:0}
    for i in range(m):
        val[(i,1)]=pow(g,i,p); val[(i,-1)]=(-pow(g,i,p))%p
    S=[None]+[(i,s) for i in range(m) for s in (1,-1)]
    pts=[]
    for w in itertools.product(S,repeat=n):
        pos=[0]*m
        for st in w:
            if st: pos[st[0]]+=st[1]
        if tuple(pos)==tuple(b): pts.append([val[st] for st in w])
    hf=[]; prev=0; d=0
    cols=[]  # evaluation columns by degree (as rows over points, we rank the transposed matrix incrementally)
    piv={}; rank=0
    def add(vec):
        nonlocal rank
        row=vec[:]
        for c,pr in piv.items():
            if row[c]:
                f=row[c]; row=[(a-f*b_)%p for a,b_ in zip(row,pr)]
        nz=next((i for i,a in enumerate(row) if a),None)
        if nz is None: return
        inv=pow(row[nz],p-2,p); piv[nz]=[a*inv%p for a in row]; rank+=1
    while rank<len(pts):
        for e in itertools.combinations_with_replacement(range(n),d):
            if max([e.count(i) for i in set(e)] or [0])>=q: continue
            vec=[1]*len(pts)
            for k,pt in enumerate(pts):
                v=1
                for i in e: v=v*pt[i]%p
                vec[k]=v
            add(vec)
            if rank==len(pts): pass
        hf.append(rank-prev); prev=rank; d+=1
    while hf and hf[-1]==0: hf.pop()
    return hf
ok=tot=0
tests=[(3,4,(0,)),(3,4,(1,)),(3,5,(1,)),(3,5,(2,)),(3,6,(2,)),(3,6,(3,)),(5,3,(1,0)),(5,4,(0,0)),(5,4,(1,0)),(5,4,(1,1)),(5,4,(2,0)),(5,4,(2,1)),(5,5,(1,1)),(5,5,(2,0)),(5,5,(3,0)),(7,4,(1,0,0)),(7,4,(1,1,0)),(7,4,(2,1,0))]
for q,n,b in tests:
    m,N,F=make(q)
    a=gr_hf(q,n,b); f=list(F(n,b,'key')); tot+=1; ok+=(a==f)
    print(q,n,b,'gr I(W):',a,'rank statistic:',f,'OK' if a==f else 'NO',flush=True)
print('direct casilla check',ok,'of',tot)
