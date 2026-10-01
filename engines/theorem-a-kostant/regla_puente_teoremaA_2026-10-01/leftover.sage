exec(preparse(open('frob.sage').read().split('res_all={}')[0]))
def search(target,pieces,maxd,cap=50):
    sols=[]; order=sorted(range(len(pieces)),key=lambda i:-sum(pieces[i].values()))
    res=dict(target); sh=[None]*len(pieces)
    def fits(pc,st): return all(res.get((la,d+st),0)>=v for (la,d),v in pc.items())
    def rec(k):
        if len(sols)>=cap: return
        if k==len(order):
            sols.append((tuple(sh),{kk:v for kk,v in res.items() if v})); return
        i=order[k]; pc=pieces[i]; md=max(d for (_,d) in pc)
        for st in range(0,maxd-md+1):
            if not fits(pc,st): continue
            for (la,d),v in pc.items(): res[(la,d+st)]-=v
            sh[i]=st; rec(k+1)
            for (la,d),v in pc.items(): res[(la,d+st)]+=v
    rec(0); return sols
for (q,n) in [(3,6)]:
    F=frob(q,n); target=coeffs(F); maxd=max(d for (_,d) in target)
    T=list(types(q,n))
    for om in range(len(T)):
        others=[i for i in range(len(T)) if i!=om]
        pcs=[coeffs(s(Ht(mu_of(T[i])))) for i in others]
        S=search(target,pcs,maxd)
        print(f'== sin el tipo {T[om]} (mu={mu_of(T[om])}): {len(S)} ajustes de los demas')
        for sh,left in S[:6]:
            # leftover as graded Schur function
            lf=sum(v*t^d*s(Partition(la)) for (la,d),v in left.items())
            ung=sum(c.subs(t=1)*s(la) for la,c in lf) if lf!=0 else 0
            target_ung=s(h(mu_of(T[om])))
            print('   desplaz.',dict(zip([T[i] for i in others],sh)),' sobrante=',lf, ' | sobrante(t=1)==h_mu?', (ung-target_ung)==0)
