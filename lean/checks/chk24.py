import itertools, numpy as np, sys
exec(open('chk21.py').read().split('fails=0; checks=0')[0])
def rank_np(M,p):
    M=np.array(M,dtype=np.int64)%p; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=np.nonzero(M[r:,c])[0]
        if len(piv)==0: continue
        i=r+piv[0]; M[[r,i]]=M[[i,r]]; inv=pow(int(M[r,c]),p-2,p); M[r]=(M[r]*inv)%p
        nz=np.nonzero(M[:,c])[0]
        for j in nz:
            if j!=r: M[j]=(M[j]-M[j,c]*M[r])%p
        r+=1
        if r==rows: break
    return r
def ideal_dim(gens,q,p,d):
    mons=list(itertools.product(range(q),repeat=d)); idx={e:i for i,e in enumerate(mons)}
    rows=[]
    for g in gens:
        for mm in mons:
            h=mul(g,{mm:1},q,p); v=[0]*len(mons)
            for e,x in h.items(): v[idx[e]]=x
            rows.append(v)
    return rank_np(rows,p) if rows else 0
def factor(a,b,c,q,p,d):  # pair a<b in {0..d}; variable index a -> a-1
    tb=add(tvar(b-1,c,d,p),const(1,d,p),p,-1)
    if a==0: return tb
    u=mul(tvar(a-1,c,d,p),tvar(b-1,c,d,p),q,p)
    return mul(tb,pw(add(u,const(1,d,p),p,-1),q-1,q,p,d),q,p)
def perms(A,B):
    for pm in itertools.permutations(B): yield list(zip(A,pm))
checks=fails=0
for p,q,r,k,maxc in [(7,7,3,1,None),(13,13,3,1,6),(11,11,5,1,6)]:
    d=2*k+1; mu=[x for x in range(1,p) if pow(x,r,p)==1]; inv={x:pow(x,p-2,p) for x in mu}
    reps=[]; 
    for z in mu:
        if z!=1 and inv[z] not in reps: reps.append(z)
    cols=list(itertools.product(mu,repeat=d))
    if maxc: 
        import random; random.seed(3)
        comp=[]; rest=[]
        for c in cols:
            c0=inv[eval('*'.join(map(str,c)))%p] if True else 1
            col=[c0]+list(c)
            C1=[v for v in range(d+1) if col[v]==1]
            ok=len(C1)%2==0 and all(sum(1 for v in col if v==z)==sum(1 for v in col if v==inv[z]) for z in reps)
            (comp if ok else rest).append(c)
        cols=random.sample(comp,min(maxc,len(comp)))+random.sample(rest,2)
    for c in cols:
        prodc=1
        for x in c: prodc=prodc*x%p
        col=[inv[prodc]]+list(c)
        # pi_c(I): all psi_J via (6.2)-free direct: use psi directly
        psis=[]
        for M in matchings(range(d+1)):
            g=const(1,d,p); surv=True
            for (a,b) in M:
                a,b=min(a,b),max(a,b)
                g=mul(g,add(tvar(b-1,c,d,p),const(1,d,p),p,-1),q,p)
                if a>0:
                    u=mul(tvar(a-1,c,d,p),tvar(b-1,c,d,p),q,p); phi={}; up=const(1,d,p)
                    for s in range(q*r): phi=add(phi,up,p); up=mul(up,u,q,p)
                    g=mul(g,phi,q,p)
            psis.append(g)
        D=ideal_dim(psis,q,p,d)
        C={z:[v for v in range(d+1) if col[v]==z] for z in mu}
        ok=len(C[1])%2==0 and all(len(C[z])==len(C[inv[z]]) for z in reps)
        if not ok:
            checks+=1; fails+= D!=0; continue
        # block ideals, computed inside R_c (block ideal dim = dim(ideal in R_c)/q^(#other vars))
        W1=[v-1 for v in C[1] if v>0]
        gP=[]
        for P in matchings(C[1]):
            g=const(1,d,p)
            for (a,b) in P: g=mul(g,factor(min(a,b),max(a,b),c,q,p,d),q,p)
            gP.append(g)
        prod=ideal_dim(gP,q,p,d)//(q**(d-len(W1)))
        for z in reps:
            Wz=[v-1 for v in C[z]+C[inv[z]] if v>0]
            gs=[]
            for s in perms(C[z],C[inv[z]]):
                g=const(1,d,p)
                for (a,b) in s: g=mul(g,factor(min(a,b),max(a,b),c,q,p,d),q,p)
                gs.append(g)
            prod*=ideal_dim(gs,q,p,d)//(q**(d-len(Wz)))
        checks+=1; fails+= D!=prod
        print(p,q,r,c,'dim',D,'product',prod); sys.stdout.flush()
print('TOTAL',checks,fails)
