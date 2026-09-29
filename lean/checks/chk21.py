import itertools
def mul(f,g,q,p):
    h={}
    for a,x in f.items():
        for b,y in g.items():
            e=tuple(i+j for i,j in zip(a,b))
            if e and max(e)>=q: continue
            h[e]=(h.get(e,0)+x*y)%p
    return {e:c for e,c in h.items() if c}
def add(f,g,p,s=1):
    h=dict(f)
    for e,c in g.items(): h[e]=(h.get(e,0)+s*c)%p
    return {e:c for e,c in h.items() if c}
def const(x,d,p): return {tuple([0]*d):x%p} if x%p else {}
def tvar(i,c,d,p):  # t_i = c_i + s_i
    return add(const(c[i],d,p),{tuple(1 if j==i else 0 for j in range(d)):1},p)
def pw(f,n,q,p,d):
    r=const(1,d,p)
    for _ in range(n): r=mul(r,f,q,p)
    return r
def isunit(f,d,p): return f.get(tuple([0]*d),0)%p!=0
def rank(rows,p):
    rows=[r[:] for r in rows]; rk=0
    for c in range(len(rows[0]) if rows else 0):
        piv=next((i for i in range(rk,len(rows)) if rows[i][c]),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]; inv=pow(rows[rk][c],p-2,p); rows[rk]=[x*inv%p for x in rows[rk]]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]: f=rows[i][c]; rows[i]=[(x-f*y)%p for x,y in zip(rows[i],rows[rk])]
        rk+=1
    return rk
def principal(f,q,p,d):
    mons=list(itertools.product(range(q),repeat=d))
    return [[mul(f,{m:1},q,p).get(e,0) for e in mons] for m in mons]
def matchings(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for b in S[1:]:
        rest=[x for x in S if x not in (a,b)]
        for M in matchings(rest): yield [(a,b)]+M
fails=0; checks=0
for p,q,r,k in [(3,3,2,1),(3,3,2,2),(5,5,2,1),(7,7,3,1),(7,7,2,1),(5,5,4,1)]:
    m=q*r; d=2*k+1; mu=[x for x in range(1,p) if pow(x,r,p)==1]
    for c in itertools.product(mu,repeat=d):
        # (i)
        for i in range(d):
            f=add(tvar(i,c,d,p),const(1,d,p),p,-1); checks+=1
            if c[i]!=1:
                if not isunit(f,d,p): fails+=1
            else:
                if pw(f,q,q,p,d): fails+=1
        # (ii)
        for j in range(d):
            for l in range(j+1,d):
                u=mul(tvar(j,c,d,p),tvar(l,c,d,p),q,p)
                phi={}; up=const(1,d,p)
                for s in range(m): phi=add(phi,up,p); up=mul(up,u,q,p)
                checks+=1
                if c[j]*c[l]%p!=1:
                    if phi: fails+=1
                else:
                    w=const(1,d,p)
                    for xi in mu:
                        if xi!=1: w=mul(w,pw(add(u,const(xi,d,p),p,-1),q,q,p,d),q,p)
                    if not isunit(w,d,p) or add(phi,mul(w,pw(add(u,const(1,d,p),p,-1),q-1,q,p,d),q,p),p,-1): fails+=1
        # (iii): matchings of {0..d}; variable index a>=1 -> t_{a-1}
        c0=pow(1 if d==0 else eval('*'.join(str(x) for x in c)),p-2,p)
        col=[c0]+list(c)
        for M in matchings(range(d+1)):
            psi=const(1,d,p); prod=const(1,d,p); surv=True
            for (a,b) in M:
                a,b=min(a,b),max(a,b)
                tb=add(tvar(b-1,c,d,p),const(1,d,p),p,-1)
                psi=mul(psi,tb,q,p); prod=mul(prod,tb,q,p)
                if a>0:
                    u=mul(tvar(a-1,c,d,p),tvar(b-1,c,d,p),q,p); phi={}; up=const(1,d,p)
                    for s in range(m): phi=add(phi,up,p); up=mul(up,u,q,p)
                    psi=mul(psi,phi,q,p); prod=mul(prod,pw(add(u,const(1,d,p),p,-1),q-1,q,p,d),q,p)
                    if col[a]*col[b]%p!=1: surv=False
            checks+=1
            if not surv:
                if psi: fails+=1
            else:
                a0=[x for x in M if 0 in x][0]; k0=max(a0)
                if col[0]*col[k0]%p!=1: fails+=1
                # psi = unit * prod : same principal ideal
                A=principal(prod,q,p,d); B=principal(psi,q,p,d)
                if rank(A,p)!=rank(B,p) or rank(A+B,p)!=rank(A,p): fails+=1
    print(p,q,r,k,'cum checks',checks,'fails',fails)
print('TOTAL',checks,fails)
