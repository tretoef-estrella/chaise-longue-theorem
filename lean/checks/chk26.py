import itertools, sys, random
exec(open('chk24.py').read().split('checks=fails=0')[0])
from math import factorial
def Qk(k,q):
    h=(q-1)//2; N=2*k+2; tot=0
    for b in itertools.product(range(N+1),repeat=h):
        if 2*sum(b)==N:
            den=1
            for x in b: den*=factorial(x)**2
            tot+=factorial(N)//den
    return tot
def closed(n,q):
    h=(q-1)//2; T=[(u,e) for u in range(h) for e in (0,1)]; c=0
    for M in itertools.product(range(len(T)),repeat=n):
        cnt={}
        for i in M: cnt[T[i]]=cnt.get(T[i],0)+1
        if all(cnt.get((u,0),0)==cnt.get((u,1),0) for u in range(h)): c+=1
    return c
def Dpoly(i,j,q,p,n,sign=True):  # D(y_i,y_j) = sum_u (-1)^u y_i^u y_j^(q-2-u)
    f={}
    for u in range(q-1):
        e=[0]*n; e[i]+=u; e[j]+=q-2-u
        f[tuple(e)]=(f.get(tuple(e),0)+((-1)**u if sign else 1))%p
    return {e:c for e,c in f.items() if c}
def reduce_box(f,b):  # drop monomials with exponent >= b
    return {e:c for e,c in f.items() if max(e,default=0)<b}
def ideal_dim_box(gens,b,p,n):
    mons=list(itertools.product(range(b),repeat=n)); idx={e:i for i,e in enumerate(mons)}; rows=[]
    for g in gens:
        for mm in mons:
            h=mul(g,{mm:1},b,p); v=[0]*len(mons)
            for e,x in h.items(): v[idx[e]]=x
            rows.append(v)
    return rank_np(rows,p) if rows else 0
checks=fails=0; neg=0; negt=0
# (A) Lemma 2.4(i): (a+b)^(q-1) b = -a b D(a,b) mod b^q, and the negative control (no signs)
for p in [3,5,7,11,13]:
    q=p; a={(1,0):1}; b={(0,1):1}
    lhs=mul(pw(add(a,b,p),q-1,q+1,p,2),b,q+1,p); lhs={e:c for e,c in lhs.items() if e[1]<q}
    for sg in (True,False):
        rhs=mul(mul(a,b,q+1,p),Dpoly(0,1,q,p,2,sg),q+1,p); rhs={e:(-c)%p for e,c in rhs.items() if e[1]<q}; rhs={e:c for e,c in rhs.items() if c}
        if sg: checks+=1; fails+= lhs!=rhs
        else: negt+=1; neg+= lhs!=rhs
print('2.4(i)',checks,fails,'neg fails',neg,'/',negt)
# (B) Lemma 6.6 via chk24 machinery: dim I_{c,1} (computed from g_P in R_c) vs dim (D_J)C and vs Q / closed counts
for p,q,r,k,samp in [(3,3,1,1,None),(5,5,1,1,None),(3,3,1,2,None),(7,7,3,1,None),(13,13,3,1,14)]:
    d=2*k+1; mu=[x for x in range(1,p) if pow(x,r,p)==1]; inv={x:pow(x,p-2,p) for x in mu}
    cols=list(itertools.product(mu,repeat=d)); random.seed(7)
    if samp: cols=random.sample(cols,samp)
    for c in cols:
        prodc=1
        for x in c: prodc=prodc*x%p
        col=[inv[prodc]]+list(c); C1=[v for v in range(d+1) if col[v]==1]; W1=[v-1 for v in C1 if v>0]
        gP=[]
        for P in matchings(C1):
            g=const(1,d,p)
            for (a,b) in P: g=mul(g,factor(min(a,b),max(a,b),c,q,p,d),q,p)
            gP.append(g)
        D=ideal_dim(gP,q,p,d)//(q**(d-len(W1))) if gP else 0
        s=len(C1)
        if s%2: ok= D==0; N=0
        else:
            kk=s//2; n=len(W1); lab={v:i for i,v in enumerate(sorted(W1))}
            DJ=[]
            for P in matchings(C1):
                f=const(1,n,p)
                for (a,b) in P:
                    a,b=min(a,b),max(a,b)
                    if a>0: f=mul(f,Dpoly(lab[a-1],lab[b-1],q,p,n),q-1,p)
                DJ.append(f)
            DC=ideal_dim_box(DJ,q-1,p,n) if n>0 else 1
            N= Qk(kk-1,q) if 0 in C1 else closed(s,q)
            ok = D==DC and D>=N
        checks+=1; fails+= not ok
        if not ok: print('FAIL',p,q,r,k,c,D,N)
    print('done',p,q,r,k,checks,fails); sys.stdout.flush()
print('TOTAL',checks,fails,'neg',neg,negt)
