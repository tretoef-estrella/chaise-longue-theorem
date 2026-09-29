import itertools, sys, random
exec(open('chk24.py').read().split('checks=fails=0')[0])
def tinv(i,c,d,p,q):  # (c_i + s_i)^{-1} = c^{-1} sum_j (-s/c)^j
    ci=pow(c[i],p-2,p); s={tuple(1 if j==i else 0 for j in range(d)):1}
    term=const(ci,d,p); res={}
    for j in range(q):
        res=add(res,term,p); term=mul(term,s,q,p); term={e:(-x*ci)%p for e,x in term.items()}
    return res
def ideal_rows(gens,q,p,d):
    mons=list(itertools.product(range(q),repeat=d)); idx={e:i for i,e in enumerate(mons)}; rows=[]
    for g in gens:
        for mm in mons:
            h=mul(g,{mm:1},q,p); v=[0]*len(mons)
            for e,x in h.items(): v[idx[e]]=x
            rows.append(v)
    return rows
def rk(rows,p): return rank_np(rows,p) if rows else 0
# direct Ibal / Iph dims in F_p[x,z]/(x^q,z^q)
def bip_dim(al,be,kind,q,p):
    d=al+be; X=lambda i:{tuple(1 if j==i else 0 for j in range(d)):1}; Z=lambda l:X(al+l)
    gens=[]
    if kind=='bal':
        for s in itertools.permutations(range(be)):
            g=const(1,d,p)
            for i in range(al): g=mul(g,pw(add(X(i),Z(s[i]),p,-1),q-1,q,p,d),q,p)
            gens.append(g)
    else:
        for i0 in range(al):
            others=[i for i in range(al) if i!=i0]
            for s in itertools.permutations(range(be)):
                g=const(1,d,p)
                for i,l in zip(others,s): g=mul(g,pw(add(X(i),Z(l),p,-1),q-1,q,p,d),q,p)
                gens.append(g)
    return rk(ideal_rows(gens,q,p,d),p)
def cnt(xs,u): return sum(1 for x in xs if x==u)
def Nbal(a,q): return sum(1 for xi in itertools.product(range(q),repeat=a) for eta in itertools.product(range(q),repeat=a) if all(cnt(xi,u)==cnt(eta,u) for u in range(q)))
def Nph(a,q): return sum(1 for xi in itertools.product(range(q),repeat=a+1) for eta in itertools.product(range(q),repeat=a) if all(cnt(eta,u)<=cnt(xi,u) for u in range(q)))
checks=fails=0; ncase={}
for p,q,r,k,samp in [(7,7,3,1,None),(13,13,3,1,10)]:
    d=2*k+1; mu=[x for x in range(1,p) if pow(x,r,p)==1]; inv={x:pow(x,p-2,p) for x in mu}
    reps=[]
    for z in mu:
        if z!=1 and inv[z] not in reps: reps.append(z)
    cols=list(itertools.product(mu,repeat=d))
    random.seed(5)
    if samp: cols=random.sample(cols,samp)
    for c in cols:
        prodc=1
        for x in c: prodc=prodc*x%p
        col=[inv[prodc]]+list(c)
        for z in reps:
            A=[v for v in range(d+1) if col[v]==z]; B=[v for v in range(d+1) if col[v]==inv[z]]
            As=[v for v in A if v>0]; Bs=[v for v in B if v>0]; W=[v-1 for v in As+Bs]
            gs=[]
            for s in (perms(A,B) if len(A)==len(B) else []):
                g=const(1,d,p)
                for (a,b) in s: g=mul(g,factor(min(a,b),max(a,b),c,q,p,d),q,p)
                gs.append(g)
            rows=ideal_rows(gs,q,p,d); D=rk(rows,p)//(q**(d-len(W)))
            if len(A)!=len(B):
                case='zero'; ok= D==0 and not gs
            else:
                # phi images of I^bal / I^ph generators inside R_c
                xv={i:add(mul(const(inv[z],d,p),tvar(i-1,c,d,p),q,p),const(1,d,p),p,-1) for i in As}
                zv={l:add(mul(const(z,d,p),tvar(l-1,c,d,p),q,p),const(1,d,p),p,-1) for l in Bs}
                if 0 not in A+B: case='bal'; big,small=list(xv.values()),list(zv.values()); nb=('bal',len(As),len(Bs)); N=Nbal(len(As),q)
                elif 0 in B: case='phB'; big,small=list(xv.values()),list(zv.values()); nb=('ph',len(As),len(Bs)); N=Nph(len(Bs),q)
                else: case='phA'; big,small=list(zv.values()),list(xv.values()); nb=('ph',len(Bs),len(As)); N=Nph(len(As),q)
                ph=[]
                if nb[0]=='bal':
                    for s in itertools.permutations(range(len(small))):
                        g=const(1,d,p)
                        for i in range(len(big)): g=mul(g,pw(add(big[i],small[s[i]],p,-1),q-1,q,p,d),q,p)
                        ph.append(g)
                else:
                    for i0 in range(len(big)):
                        oth=[i for i in range(len(big)) if i!=i0]
                        for s in itertools.permutations(range(len(small))):
                            g=const(1,d,p)
                            for i,l in zip(oth,s): g=mul(g,pw(add(big[i],small[l],p,-1),q-1,q,p,d),q,p)
                            ph.append(g)
                rows2=ideal_rows(ph,q,p,d); r2=rk(rows2,p); r12=rk(rows+rows2,p)
                Dbip=bip_dim(nb[1],nb[2],nb[0],q,p)
                ok = (r12==r2==D*q**(d-len(W)))
            checks+=1; fails+= not ok; ncase[case]=ncase.get(case,0)+1
            if not ok: print('FAIL',p,q,r,k,c,z,case)
    print('done',p,q,r,k,checks,fails,ncase); sys.stdout.flush()
print('TOTAL',checks,fails,ncase)
