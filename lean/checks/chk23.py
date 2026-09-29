import itertools, random
random.seed(1)
exec(open('chk21.py').read().split('fails=0; checks=0')[0])
def ideal_dim(gens,q,p,d):
    mons=list(itertools.product(range(q),repeat=d)); rows=[]
    for g in gens:
        for mm in mons:
            h=mul(g,{mm:1},q,p)
            rows.append([h.get(e,0) for e in mons])
    return rank(rows,p) if rows else 0
def randpoly(vars_,q,p,d,c,nterms=3):
    # polynomial in t_i (i in vars_), expressed in s = t - c coordinates
    f={}
    for _ in range(nterms):
        g=const(random.randrange(1,p),d,p)
        for i in vars_:
            e=random.randrange(q)
            g=mul(g,pw(tvar(i,c,d,p),e,q,p,d),q,p)
        f=add(f,g,p)
    return f
checks=fails=0
for p,q in [(3,3),(5,5),(3,9)]:
  for blocks in ([[0],[1]],[[0],[1,2]],[[0],[1],[2]],[[0,1],[2]]):
    d=sum(len(b) for b in blocks)
    if q**d>800: continue
    for trial in range(6):
        c=[random.randrange(p) for _ in range(d)]
        E=[[randpoly(b,q,p,d,c) for _ in range(random.randrange(1,3))] for b in blocks]
        dims=[ideal_dim(Eb,q,p,d)//(q**(d-len(b))) for Eb,b in zip(E,blocks)]  # ideal in R(W) of block gens = I_j ⊗ R(rest)
        prods=[]
        for choice in itertools.product(*E):
            g=const(1,d,p)
            for x in choice: g=mul(g,x,q,p)
            prods.append(g)
        D=ideal_dim(prods,q,p,d); P=1
        for x in dims: P*=x
        checks+=1; fails+= D!=P
print('checks',checks,'fails',fails)
