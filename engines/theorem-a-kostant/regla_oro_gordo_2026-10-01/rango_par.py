# fibre-rank statistic for even q=2m: loopless walks (steps +-e_i), ending at 0 (n even) or e_1 (n odd)
import re
from functools import lru_cache
def run(q,n):
    m=q//2
    S=[]
    for i in range(m):
        for s in (1,-1):
            v=[0]*m; v[i]=s; S.append(tuple(v))
    sub=lambda b,c: tuple(x-y for x,y in zip(b,c))
    @lru_cache(None)
    def N(j,b):
        if j==0: return 1 if all(x==0 for x in b) else 0
        if sum(abs(x) for x in b)>j: return 0
        return sum(N(j-1,sub(b,c)) for c in S)
    @lru_cache(None)
    def F(j,b):
        if j==0: return (1,) if all(x==0 for x in b) else ()
        ch=sorted([(N(j-1,sub(b,c)),k,sub(b,c)) for k,c in enumerate(S)],key=lambda x:(-x[0],x[1]))
        poly={}
        for r,(cnt,k,bb) in enumerate(ch):
            if cnt==0: continue
            for d,a in enumerate(F(j-1,bb)): poly[d+r]=poly.get(d+r,0)+a
        L=max(poly)+1 if poly else 0
        return tuple(poly.get(d,0) for d in range(L))
    end=tuple([n%2]+[0]*(m-1))
    return list(F(n,end))
ok=tot=0
for fn in ['tipoC.log','tipoC_impar.log']:
    for line in open(fn):
        mm=re.match(r'q=(\d+) n=(\d+) HF=\{(.*)\}',line)
        if not mm: continue
        q,n=int(mm[1]),int(mm[2]); hf=[int(x) for x in mm[3].split(',')]
        r=run(q,n); tot+=1; ok+=(r==hf); print(q,n,r==hf, '' if r==hf else (r,hf))
print('even-q rank statistic',ok,'of',tot)
