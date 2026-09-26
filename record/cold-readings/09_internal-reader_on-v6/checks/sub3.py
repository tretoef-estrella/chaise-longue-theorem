import itertools
def matchings(s):
    if not s: yield []; return
    a=s[0]
    for i in range(1,len(s)):
        for m in matchings(s[1:i]+s[i+1:]): yield [(a,s[i])]+m
Ms=list(matchings(list(range(6))))
p=3
# polys over F3 in y1..y5 squarefree: dict mask->coef
def mul(f,g):
    h={}
    for a,c in f.items():
        for b,d in g.items():
            if a&b: continue
            h[a|b]=(h.get(a|b,0)+c*d)%p
    return {k:v for k,v in h.items() if v}
def var(i): return 1<<(i-1)
vecs=[]
for J in Ms:
    D={0:1}
    for a,b in J:
        if a==0: continue
        D=mul(D,{var(b):1,var(a):p-1})
    rows=[]
    for U in range(32):
        g=mul(D,{U:1})
        if g:
            v=[0]*32
            for k,c in g.items(): v[k]=c
            rows.append(v)
    vecs.append(rows)
def rank(rows):
    rows=[r[:] for r in rows]; r=0
    for c in range(32):
        piv=None
        for i in range(r,len(rows)):
            if rows[i][c]%p: piv=i;break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],p-2,p); rows[r]=[x*inv%p for x in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][c]%p:
                f=rows[i][c]; rows[i]=[(x-f*y)%p for x,y in zip(rows[i],rows[r])]
        r+=1
    return r
# Gamma_J sets over T={1,2} (mod 3 values 1,2 ; negation x->3-x)
pts=list(itertools.product([1,2],repeat=5))
GJ=[]
for J in Ms:
    s=set()
    for pt in pts:
        A=(None,)+pt
        if all((A[a]+A[b])%3==0 for a,b in J if a!=0): s.add(pt)
    GJ.append(s)
fails=0; viol=0; worst=0
for mask in range(1,1<<15):
    K=[i for i in range(15) if mask>>i&1]
    d=rank([v for i in K for v in vecs[i]])
    g=len(set().union(*[GJ[i] for i in K]))
    if d<g: fails+=1; worst=max(worst,g-d)
    if d>g: viol+=1
print("fails",fails,"worst",worst,"viol(>)",viol)
