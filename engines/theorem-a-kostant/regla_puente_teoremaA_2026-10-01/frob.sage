import re, itertools
R.<t> = QQ[]
K = FractionField(R)
Sym = SymmetricFunctions(K); s=Sym.schur(); p=Sym.power(); h=Sym.homogeneous()
Ht = Sym.macdonald(q=0).Ht()
data={}
for line in open('traces.log'):
    m=re.match(r'q=(\d+) n=(\d+) lam=\{(.*)\} tr=\{(.*)\}',line)
    if m:
        q,n=int(m[1]),int(m[2]); lam=Partition([int(x) for x in m[3].split(',')]); tr=[int(x) for x in m[4].split(',')]
        data.setdefault((q,n),{})[lam]=tr
def frob(q,n):
    D=data[(q,n)]; L=max(len(v) for v in D.values())
    F=0
    for lam,tr in D.items():
        poly=sum(QQ(tr[d])*t^d for d in range(len(tr)))
        F+= poly*p(lam)/lam.centralizer_size()
    return s(F)
def types(q,n):
    M=(q-1)//2
    for a in itertools.product(range(n//2+1),repeat=M):
        a0=n-2*sum(a)
        if a0>=0: yield (a0,)+a
def mu_of(tp): return Partition(sorted([m for m in [tp[0]]+[x for x in tp[1:] for _ in (0,1)] if m>0],reverse=True))
def coeffs(f):  # dict (lambda, degree) -> integer
    out={}
    for la,c in f:
        c=R(c)
        for d,v in enumerate(c.list()):
            if v: out[(la,d)]=out.get((la,d),0)+int(v)
    return out
res_all={}
for (q,n) in sorted(data):
    F=frob(q,n)
    # check 1: ungraded = sum of h_mu over types
    ung = s(sum(h(mu_of(tp)) for tp in types(q,n)))
    F1 = sum(c.subs(t=1)*s(la) for la,c in F)
    ok_ung = (s(F1)-ung)==0
    # pieces
    T=list(types(q,n)); pieces=[coeffs(s(Ht(mu_of(tp)))) for tp in T]
    target=coeffs(F)
    maxd=max(d for (_,d) in target)
    sols=[]
    order=sorted(range(len(T)),key=lambda i:-sum(pieces[i].values()))
    res=dict(target); sh=[None]*len(T)
    def fits(pc,st):
        return all(res.get((la,d+st),0)>=v for (la,d),v in pc.items())
    def rec(k):
        if len(sols)>=20: return
        if k==len(order):
            if all(v==0 for v in res.values()): sols.append(tuple(sh))
            return
        i=order[k]; pc=pieces[i]; md=max(d for (_,d) in pc)
        for st in range(0,maxd-md+1):
            if not fits(pc,st): continue
            for (la,d),v in pc.items(): res[(la,d+st)]-=v
            sh[i]=st; rec(k+1)
            for (la,d),v in pc.items(): res[(la,d+st)]+=v
    rec(0)
    print(f'q={q} n={n} ungraded=perm.char:{ok_ung}  tipos={T}  ajustes_Frobenius={len(sols)} ej={sols[:3]}',flush=True)
    if not sols and n<=6:
        print('   carácter graduado por grado:')
        for d in range(maxd+1):
            row=[(tuple(la),v) for (la,dd),v in sorted(target.items()) if dd==d]
            print('    d=%d'%d, row)
