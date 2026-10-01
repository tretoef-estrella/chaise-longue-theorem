# Fibre-rank statistic on closed walks on Z^m with loops (m=(q-1)/2).
# F_j(b) = sum over steps c ordered by N_{j-1}(b-c) desc: t^rank F_{j-1}(b-c)
import sys, itertools
from functools import lru_cache
def steps(m):
    out=[tuple([0]*m)]
    for i in range(m):
        for s in (1,-1):
            v=[0]*m; v[i]=s; out.append(tuple(v))
    return out
def run(q,n,tiebreak=0):
    m=(q-1)//2; S=steps(m)
    @lru_cache(None)
    def N(j,b):
        if j==0: return 1 if all(x==0 for x in b) else 0
        if sum(abs(x) for x in b)>j: return 0
        return sum(N(j-1,tuple(bi-ci for bi,ci in zip(b,c))) for c in S)
    @lru_cache(None)
    def F(j,b):
        if j==0: return (1,) if all(x==0 for x in b) else ()
        ch=[(N(j-1,tuple(bi-ci for bi,ci in zip(b,c))),k,tuple(bi-ci for bi,ci in zip(b,c))) for k,c in enumerate(S)]
        if tiebreak==0: ch.sort(key=lambda x:(-x[0],x[1]))
        else: ch.sort(key=lambda x:(-x[0],-x[1]))
        poly={}
        for r,(cnt,k,bb) in enumerate(ch):
            if cnt==0: continue
            for d,a in enumerate(F(j-1,bb)):
                poly[d+r]=poly.get(d+r,0)+a
        L=max(poly)+1 if poly else 0
        return tuple(poly.get(d,0) for d in range(L))
    return list(F(n,tuple([0]*m)))
data={}
for line in open('../regla_puente_teoremaA_2026-10-01/hfall.log'):
    p=line.split(); q=int(p[0][2:]); n=int(p[1][2:])
    hf=[int(x) for x in line.split('{')[1].split('}')[0].split(',')]
    data[(q,n)]=hf
ok=0
for (q,n),hf in sorted(data.items()):
    a=run(q,n,0); b=run(q,n,1)
    print(q,n,'stat=',a,'data=',hf,'MATCH' if a==hf else 'NO', 'tieindep' if a==b else 'TIE-DEP')
    ok+= a==hf
print('matches',ok,'of',len(data))
