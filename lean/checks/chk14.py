import sys, itertools, math
BIG=10**40
src=open('chk8.py').read().split('fails=checks=0')[0].replace('P=101',f'P={BIG}',1)
exec(src)
def sym(x): x%=BIG; return x-BIG if x>BIG//2 else x
def resPart(M,h):
    parts=[]
    for u in range(1,h+1):
        a=M.count(u); b=M.count(-u)
        if a!=b: parts.append(abs(a-b))
    return tuple(sorted(parts,reverse=True))
def introws(Lam,m,q):
    gens=[prod(p,m,q) for lam in Lam for p in patterns(lam,range(m)) if sum(lam)<=m and (m-sum(lam))%2==0]
    Ms=monos(m,q); idx={e:i for i,e in enumerate(Ms)}
    rows=[]
    for g in gens:
        for mo in Ms:
            f=pmul(g,{mo:1},q); v=[0]*len(Ms)
            for k,c in f.items(): v[idx[k]]=sym(c)
            if any(v): rows.append(v)
    return rows,len(Ms)
def elementary_divisors(rows,n):
    # integer Smith normal form diagonal (nonzero), via row/col gcd elimination
    A=[r[:] for r in rows]; divs=[]
    R=len(A); C=n
    t=0
    while True:
        # find nonzero entry with smallest abs among rows>=t, cols>=t
        best=None
        for i in range(t,len(A)):
            for j in range(t,C):
                if A[i][j] and (best is None or abs(A[i][j])<abs(A[best[0]][best[1]])): best=(i,j)
        if best is None: break
        i,j=best
        A[t],A[i]=A[i],A[t]
        for r in A: r[t],r[j]=r[j],r[t]
        while True:
            p=A[t][t]; done=True
            for i in range(t+1,len(A)):
                if A[i][t]:
                    qq=A[i][t]//p; A[i]=[a-qq*b for a,b in zip(A[i],A[t])]
                    if A[i][t]: done=False
            for j in range(t+1,C):
                if A[t][j]:
                    qq=A[t][j]//p
                    for r in A: r[j]-=qq*r[t]
                    if A[t][j]: done=False
            if done:
                # ensure p divides all remaining entries
                bad=None
                for i in range(t+1,len(A)):
                    for j in range(t+1,C):
                        if A[i][j]%p: bad=i;break
                    if bad is not None: break
                if bad is None: break
                A[t]=[a+b for a,b in zip(A[t],A[bad])]; continue
            # move smallest to pivot
            best=None
            for i in range(t,len(A)):
                if A[i][t] and (best is None or abs(A[i][t])<abs(A[best][t])): best=i
            for j in range(t,C):
                if A[t][j] and abs(A[t][j])<abs(A[t][t]):
                    for r in A: r[t],r[j]=r[j],r[t]
            if best is not None and abs(A[best][t])<abs(A[t][t]): A[t],A[best]=A[best],A[t]
        divs.append(abs(A[t][t]))
        A=[r for idx_,r in enumerate(A) if idx_<=t or any(r[t+1:])]
        t+=1
    return divs
tot=bad=0
for q,mmax in ((3,4),(5,3),(7,2)):
    h=(q-1)//2; T=[s*u for u in range(1,h+1) for s in (1,-1)]
    for m in range(1,mmax+1):
        for Lam in downsets(parts_list(m,h)):
            if not Lam: continue
            rows,n=introws(Lam,m,q)
            d=elementary_divisors(rows,n)
            Z=sum(1 for M in itertools.product(T,repeat=m) if resPart(list(M),h) in Lam)
            tot+=1
            ok=(len(d)==Z and all(x==1 for x in d))
            if not ok: bad+=1; print('FAIL',q,m,Lam,len(d),Z,[x for x in d if x!=1][:5])
print('cases',tot,'fails',bad)
