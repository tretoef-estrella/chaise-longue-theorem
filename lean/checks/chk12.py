exec(open('chk8.py').read().split('fails=checks=0')[0])
import itertools
def evalp(f,pt):
    s=0
    for e,c in f.items():
        t=c
        for x,k in zip(pt,e): t=t*pow(x,k,P)%P
        s=(s+t)%P
    return s
def resPartF(M,T):
    seen=set(); parts=[]
    for u in T:
        if u in seen: continue
        v=(-u)%P; seen|={u,v}
        a=M.count(u); b=M.count(v)
        if a!=b: parts.append(abs(a-b))
    return tuple(sorted(parts,reverse=True))
bad=tot=0; evbad=0
for q in (3,5):
    T=[x for x in range(1,P) if pow(x,q-1,P)==1]; h=(q-1)//2
    for a in T:
        for b in T:
            if a==b: continue
            d=D(0,1,2,q); val=evalp(d,(a,b))
            if (b==(-a)%P) != (val!=0): evbad+=1
    for m in range(1,5 if q==3 else 4):
        for lam in parts_list(m,h):
            for pat in patterns(lam,range(m)):
                g=prod(pat,m,q)
                for pt in itertools.product(T,repeat=m):
                    if evalp(g,pt):
                        tot+=1
                        if not wdom(resPartF(list(pt),T),lam): bad+=1
print('eval failures',evbad,'nonzero evaluations',tot,'support failures',bad)
