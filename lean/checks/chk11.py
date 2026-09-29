exec(open('chk8.py').read().split('fails=checks=0')[0])
import random, itertools
random.seed(1)
def evalp(f,pt): 
    s=0
    for e,c in f.items():
        t=c
        for x,k in zip(pt,e): t=t*pow(x,k,P)%P
        s=(s+t)%P
    return s
bad=tot=0
for q in (3,5,11):
    T=[x for x in range(1,P) if pow(x,q-1,P)==1]; assert len(T)==q-1
    for m in (1,2,3):
        if (q-1)**m>1400: continue
        for trial in range(15):
            gens=[]
            for _ in range(random.randint(1,3)):
                d=random.randint(0,m*(q-2))
                mons=[e for e in itertools.product(range(q-1),repeat=m) if sum(e)==d]
                g={e:random.randrange(P) for e in random.sample(mons,min(len(mons),random.randint(1,3)))}
                g={k:v for k,v in g.items() if v}
                if g: gens.append(g)
            if not gens: continue
            V,M,idx=ideal(gens,m,q)
            Sig=sum(1 for pt in itertools.product(T,repeat=m) if any(evalp(g,pt) for g in gens))
            tot+=1
            if len(V)>Sig: bad+=1; print('FAIL',q,m,len(V),Sig)
print('cases',tot,'failures',bad)
