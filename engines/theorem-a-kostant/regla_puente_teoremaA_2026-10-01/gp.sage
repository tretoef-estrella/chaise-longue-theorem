import re, itertools
R.<t> = QQ[]
Sym = SymmetricFunctions(FractionField(R))
s = Sym.schur()
Ht = Sym.macdonald(q=0).Ht()   # modified Macdonald at q=0 = modified Hall-Littlewood H~_mu(x;t)
def gp_hilb(mu):
    mu=Partition(sorted([m for m in mu if m>0],reverse=True)); n=sum(mu)
    f = s(Ht(mu))
    # Hilbert series = sum_lambda f^lambda * coeff
    tot = sum(c*StandardTableaux(la).cardinality() for la,c in f)
    p = R(tot)
    return [int(p[i]) for i in range(p.degree()+1)]
# sanity: GP Hilbert series dims = multinomial
assert sum(gp_hilb([2,1,1]))==12 and sum(gp_hilb([2,2]))==6
print('GP(211)=',gp_hilb([2,1,1]),' GP(22)=',gp_hilb([2,2]),flush=True)
HF={}
for line in open('hf.log'):
    m=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\} total',line)
    if m: HF[(int(m[1]),int(m[2]))]=[int(x) for x in m[3].split(',')]
def types(q,n):
    M=(q-1)//2
    for a in itertools.product(range(n//2+1),repeat=M):
        a0=n-2*sum(a)
        if a0>=0: yield (a0,)+a
def solve(h,pieces,cap=40):
    sols=[]; L=len(h); order=sorted(range(len(pieces)),key=lambda i:-sum(pieces[i]))
    res=h[:]; sh=[None]*len(pieces)
    def rec(k):
        if len(sols)>=cap: return
        if k==len(order):
            if all(x==0 for x in res): sols.append(tuple(sh))
            return
        i=order[k]; p=pieces[i]
        for st in range(0,L-len(p)+1):
            if any(res[st+j]<x for j,x in enumerate(p)): continue
            for j,x in enumerate(p): res[st+j]-=x
            sh[i]=st; rec(k+1)
            for j,x in enumerate(p): res[st+j]+=x
    rec(0); return sols
for (q,n),h in sorted(HF.items()):
    T=list(types(q,n)); pieces=[gp_hilb([t[0]]+[x for x in t[1:] for _ in (0,1)]) for t in T]
    S=solve(h,pieces)
    print(f'q={q} n={n} tipos={T} sols={len(S)}{"+" if len(S)>=40 else ""} ej={S[:4]}',flush=True)
