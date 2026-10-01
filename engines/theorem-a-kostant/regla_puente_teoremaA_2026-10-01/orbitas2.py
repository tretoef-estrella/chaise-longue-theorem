import re, itertools, sys
exec(open('orbitas.py').read().split('HF={}')[0])
HF={}
for line in open('hf.log'):
    m=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\} total',line)
    if m: HF[(int(m[1]),int(m[2]))]=[int(x) for x in m[3].split(',')]
def types(q,n):
    M=(q-1)//2
    for a in itertools.product(range(n//2+1),repeat=M):
        a0=n-2*sum(a)
        if a0>=0: yield (a0,)+a
def solve(h,pieces,cap=40):
    sols=[]; L=len(h)
    order=sorted(range(len(pieces)),key=lambda i:-sum(pieces[i]))
    res=h[:]; sh=[None]*len(pieces)
    def rec(k):
        if len(sols)>=cap: return
        if k==len(order):
            if all(x==0 for x in res): sols.append(tuple(sh))
            return
        i=order[k]; p=pieces[i]
        for s in range(0,L-len(p)+1):
            ok=True
            for j,x in enumerate(p):
                if res[s+j]<x: ok=False;break
            if not ok: continue
            for j,x in enumerate(p): res[s+j]-=x
            sh[i]=s; rec(k+1)
            for j,x in enumerate(p): res[s+j]+=x
    rec(0); return sols
for (q,n),h in sorted(HF.items()):
    T=list(types(q,n)); pieces=[qmult([m for m in [t[0]]+[x for x in t[1:] for _ in (0,1)] if m>0]) for t in T]
    S=solve(h,pieces)
    print(f'q={q} n={n} tipos={T} soluciones={len(S)}{"+" if len(S)>=40 else ""} ej={S[:3]}',flush=True)
