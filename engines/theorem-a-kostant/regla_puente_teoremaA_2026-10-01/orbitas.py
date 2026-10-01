import re, itertools
from math import factorial
def poly_mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def qint(k): return [1]*k if k>0 else [1]
def qfact(k):
    r=[1]
    for i in range(1,k+1): r=poly_mul(r,qint(i))
    return r
def poly_div(a,b):
    a=a[:]; out=[0]*(len(a)-len(b)+1)
    for i in range(len(out)):
        c=a[i]//b[0]; out[i]=c
        for j,y in enumerate(b): a[i+j]-=c*y
    assert all(x==0 for x in a), 'no exacta'
    return out
def qmult(mu):
    n=sum(mu); r=qfact(n)
    for m in mu: r=poly_div(r,qfact(m))
    return r
HF={}
for line in open('hf.log'):
    m=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\} total',line)
    if m: HF[(int(m[1]),int(m[2]))]=[int(x) for x in m[3].split(',')]
def types(q,n):
    M=(q-1)//2
    for a in itertools.product(range(n//2+1),repeat=M):
        a0=n-2*sum(a)
        if a0>=0: yield (a0,)+a
for (q,n),h in sorted(HF.items()):
    T=list(types(q,n))
    pieces=[]
    for t in T:
        mu=[t[0]]+[x for x in t[1:] for _ in (0,1)]
        pieces.append(qmult([m for m in mu if m>0]))
    # brute-force shifts in 0..n*(q-1)
    L=len(h); sols=[]
    rng=range(0,L)
    for sh in itertools.product(rng,repeat=len(T)):
        s=[0]*L; ok=True
        for p,k in zip(pieces,sh):
            if k+len(p)>L: ok=False;break
            for i,x in enumerate(p): s[k+i]+=x
        if ok and s==h: sols.append(sh)
    print(f'q={q} n={n} tipos(a0,a1..)={T} -> desplazamientos posibles: {sols[:6]}{" ..." if len(sols)>6 else ""} ({len(sols)})')
