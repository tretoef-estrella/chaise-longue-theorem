import itertools, sys
P=101
def parts_list(m,h):
    res=[]
    def gen(n,maxp,cur):
        if n==0: res.append(tuple(cur)); return
        for x in range(min(n,maxp),0,-1): gen(n-x,x,cur+[x])
    for s in range(m%2,m+1,2):
        tmp=[]; res0=len(res); gen(s,s,[])
    return [p for p in res if len(p)<=h]
def S(t,mu): return sum(mu[:t])
def wdom(a,b): return all(S(t,a)<=S(t,b) for t in range(1,max(len(a),len(b))+2))
def colLen(lam,c): return sum(1 for x in lam if x>=c)
def subE(mu,j): l=list(mu); l[j-1]-=1; return tuple(sorted([x for x in l if x>0],reverse=True))
def addE(mu,j): l=list(mu); l[j-1]+=1; return tuple(sorted(l,reverse=True))
def addOne(mu): return tuple(sorted(list(mu)+[1],reverse=True))
def opt(mu,L,p):
    l=len(mu)
    if p<=l: return subE(mu,p)
    if p<=L-l: return addOne(mu)
    return addE(mu,L+1-p)
# polynomials: dict exps-tuple -> coef, in C_m with exps < q-1
def pmul(f,g,q):
    r={}
    for a,x in f.items():
        for b,y in g.items():
            e=tuple(i+j for i,j in zip(a,b))
            if max(e,default=0)>=q-1: continue
            r[e]=(r.get(e,0)+x*y)%P
    return {k:v for k,v in r.items() if v}
def var(i,m): e=[0]*m; e[i]=1; return {tuple(e):1}
def const(m): return {tuple([0]*m):1}
def padd(f,g,s=1):
    r=dict(f)
    for k,v in g.items(): r[k]=(r.get(k,0)+s*v)%P
    return {k:v for k,v in r.items() if v}
def D(a,b,m,q):
    r={}
    for i in range(q-1):
        e=[0]*m; e[a]+=i; e[b]+=q-2-i
        r=padd(r,{tuple(e):(-1)**i%P})
    return r
def Delta(B,m,q):
    B=sorted(B); r=const(m)
    for c in range(len(B)):
        for d in range(c+1,len(B)): r=pmul(r,padd(var(B[d],m),var(B[c],m),-1),q)
    return r
def patterns(lam,I):
    I=list(I); npairs=(len(I)-sum(lam))//2
    cols=[colLen(lam,c) for c in range(1,(lam[0] if lam else 0)+1)]
    out=[]
    def pairs_rec(rem,k,acc):
        if k==0: blocks_rec(rem,0,acc,[]); return
        if len(rem)<2: return
        a=rem[0]
        # a either in a pair or not
        for b in rem[1:]:
            pairs_rec([x for x in rem if x not in (a,b)],k-1,acc+[(a,b)])
        pairs_rec_skip(rem,k,acc)
    def pairs_rec_skip(rem,k,acc):
        pass
    # simpler: choose pair set then blocks
    res=[]
    for pairset in choose_pairs(I,npairs):
        used=set(x for pr in pairset for x in pr); rest=[x for x in I if x not in used]
        for bl in assign_blocks(rest,cols): res.append((pairset,bl))
    return res
def choose_pairs(I,k):
    if k==0: yield []; return
    I=list(I)
    for idx,a in enumerate(I):
        for b in I[idx+1:]:
            rest=[x for x in I[idx+1:] if x!=b]
            for tail in choose_pairs(rest,k-1): yield [(a,b)]+tail
def assign_blocks(rest,cols):
    if not cols:
        if not rest: yield []
        return
    for B in itertools.combinations(rest,cols[0]):
        r2=[x for x in rest if x not in B]
        for t in assign_blocks(r2,cols[1:]): yield [B]+t
def prod(pat,m,q):
    pairset,bl=pat; r=const(m)
    for a,b in pairset: r=pmul(r,D(a,b,m,q),q)
    for B in bl: r=pmul(r,Delta(B,m,q),q)
    return r
def monos(m,q): return list(itertools.product(range(q-1),repeat=m))
def rowreduce(rows,ncol):
    basis=[]; piv=[]
    for r in rows:
        r=r[:]
        for (pc,b) in zip(piv,basis):
            if r[pc]: c=r[pc]; r=[(x-c*y)%P for x,y in zip(r,b)]
        nz=next((i for i,x in enumerate(r) if x),None)
        if nz is None: continue
        inv=pow(r[nz],P-2,P); r=[x*inv%P for x in r]
        for i,(pc,b) in enumerate(zip(piv,basis)):
            if b[nz]: c=b[nz]; basis[i]=[(x-c*y)%P for x,y in zip(b,r)]
        basis.append(r); piv.append(nz)
    return basis
def ideal(gens,m,q):
    M=monos(m,q); idx={e:i for i,e in enumerate(M)}
    rows=[]
    for g in gens:
        for mo in M:
            f=pmul(g,{mo:1},q)
            v=[0]*len(M)
            for k,c in f.items(): v[idx[k]]=c
            rows.append(v)
    return rowreduce(rows,len(M)),M,idx
def VLam(Lam,I,m,q):
    gens=[prod(p,m,q) for lam in Lam for p in patterns(lam,I) if sum(lam)<=len(I) and (len(I)-sum(lam))%2==0]
    return ideal(gens,m,q)
def W(basisV,M,j,q,m):
    # f in V with deg_y1 <= j : coefficient space
    # solve: combos of basis with zero coeff on monomials with e[0]>j -> do elimination treating those columns first
    ncol=len(M)
    order=[i for i,e in enumerate(M) if e[0]>j]+[i for i,e in enumerate(M) if e[0]<=j]
    rows=[[r[i] for i in order] for r in basisV]
    red=rowreduce(rows,ncol)
    nb=sum(1 for e in M if e[0]>j)
    sub=[r for r in red if all(x==0 for x in r[:nb])]
    # back to original order then take coeff of y1^j
    inv={o:k for k,o in enumerate(order)}
    Mm1=monos(m-1,q); idx1={e:i for i,e in enumerate(Mm1)}
    out=[]
    for r in sub:
        v=[0]*len(Mm1)
        for i,e in enumerate(M):
            if e[0]==j: v[idx1[e[1:]]]=r[inv[i]]
        out.append(v)
    return rowreduce(out,len(Mm1))
def contains(A,B):
    return len(rowreduce(A+B,len(A[0]) if A else 1))==len(A) if B else True
def downsets(Par):
    n=len(Par); res=[]
    for mask in range(1<<n):
        s=[Par[i] for i in range(n) if mask>>i&1]
        ok=all(Par[j] in s for i in range(n) if mask>>i&1 for j in range(n) if wdom(Par[j],Par[i]))
        if ok: res.append(s)
    return res
fails=checks=0
for q,mmax in ((3,5),(5,4),(7,3)):
    h=(q-1)//2; L=q-1
    for m in range(1,mmax+1):
        Par=parts_list(m,h); Par1=parts_list(m-1,h)
        for Lam in downsets(Par):
            if not Lam: continue
            V,M,idx=VLam(Lam,range(m),m,q)
            for i in range(q-1):
                Lami=[mu for mu in Par1 if sum(1 for p in range(1,L+1) if opt(mu,L,p) in Lam)>i]
                if not Lami: continue
                Vi,_,_=VLam(Lami,range(m-1),m-1,q)
                Wj=W(V,M,q-2-i,q,m)
                checks+=1
                if not contains(Wj,Vi): fails+=1; print('FAIL',q,m,Lam,i)
        print('q',q,'m',m,'done checks',checks,'fails',fails,flush=True)
print('TOTAL checks',checks,'fails',fails)
