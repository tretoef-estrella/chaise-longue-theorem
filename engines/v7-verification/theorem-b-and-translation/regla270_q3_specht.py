# q=3: Lambda = F3[x_0..x_{N-1}]/(x_i^2). Check (i) dim sum_J sigma_J Lambda = C(N,N/2),
# graded = f^{(N-r,r)}; (ii) b = dim Lambda / cap_J I_J Lambda by direct intersection (N<=6).
import itertools, math
p=3
def matchings(s):
    s=list(s)
    if not s: yield []; return
    a=s[0]
    for i in range(1,len(s)):
        rest=s[1:i]+s[i+1:]
        for m in matchings(rest): yield [(a,s[i])]+m
def rank_mod(rows,ncols):
    rows=[r[:] for r in rows]; r=0
    for c in range(ncols):
        piv=None
        for i in range(r,len(rows)):
            if rows[i][c]%p: piv=i;break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],p-2,p); rows[r]=[(v*inv)%p for v in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][c]%p:
                f=rows[i][c]; rows[i]=[(a-f*b)%p for a,b in zip(rows[i],rows[r])]
        r+=1
    return r
def poly_mul(P,Q):  # squarefree polys: dict frozenset->coef
    R={}
    for s,a in P.items():
        for t,b in Q.items():
            if s&t: continue
            u=s|t; R[u]=(R.get(u,0)+a*b)%p
    return {k:v for k,v in R.items() if v}
for N in (4,6,8):
    V=range(N)
    mons=[frozenset(c) for d in range(N+1) for c in itertools.combinations(V,d)]
    idx={m:i for i,m in enumerate(mons)}
    tot=0; graded={}
    rows=[]
    for J in matchings(V):
        sig={frozenset():1}
        for a,b in J: sig=poly_mul(sig,{frozenset([a]):1,frozenset([b]):-1%p})
        for m in mons:
            pr=poly_mul(sig,{m:1})
            if pr:
                row=[0]*len(mons)
                for k,v in pr.items(): row[idx[k]]=v
                rows.append(row)
    rk=rank_mod(rows,len(mons))
    f=[math.comb(N,r)-(math.comb(N,r-1) if r else 0) for r in range(N//2+1)]
    print("N",N,"dim sum sigma_J Lambda =",rk,"C(N,N/2) =",math.comb(N,N//2),"Specht sum",sum(f))
