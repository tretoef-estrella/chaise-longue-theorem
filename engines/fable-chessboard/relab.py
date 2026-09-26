# relab.py — Fable 12: reduced top forms of the relations Rel(X;M) : sum_p e_p(Z minus X) h_{M-p}(X) = 0 on W (M odd),
# Z = y u {s,s'}; anchors kept FORMAL (s1 = s+s', s2 = s s'); y-exponents reduced by x^q -> x.  Prints y-degree and top form.
import itertools, sys
from grepy_polys import add, mul, mono, e_
def red(P,q,nv):
    R={}
    for m,v in P.items():
        m=list(m)
        for i in range(nv):
            while m[i]>=q: m[i]-=q-1
        m=tuple(m); R[m]=R.get(m,0)+v
    return {m:v%3 for m,v in R.items() if v%3}
def hX(nv,X,K):
    if K<0: return {}
    R={}
    for comb in itertools.combinations_with_replacement(X,K):
        e=[0]*nv
        for i in comb: e[i]+=1
        R[tuple(e)]=R.get(tuple(e),0)+1
    return R
def rel(n,q,X,M):
    nv=n+2; s1=n; s2=n+1   # formal anchor slots
    U=[i for i in range(n) if i not in X]
    R={}
    for k in range(0,len(U)+1):
        H=add(add(hX(nv,X,M-k),mul(mono(nv,{s1:1}),hX(nv,X,M-k-1))),mul(mono(nv,{s2:1}),hX(nv,X,M-k-2)))
        R=add(R,mul(e_(nv,U,k),H))
    return red(R,q,n)
def top(P,n):
    if not P: return -1,{}
    d=max(sum(m[:n]) for m in P); return d,{m:v for m,v in P.items() if sum(m[:n])==d}
def show(P,n):
    names='abcdefghijk'[:n]+'ST'
    out=[]
    for m,v in sorted(P.items()):
        t='*'.join('%s^%d'%(names[i],e) if e>1 else names[i] for i,e in enumerate(m) if e)
        out.append(('%+d'%v)+(t or '1'))
    return ' '.join(out)
if __name__=='__main__':
    n=int(sys.argv[1]); q=int(sys.argv[2]); X=[int(c) for c in sys.argv[3].split(',')]
    for M in range(int(sys.argv[4]),int(sys.argv[5])+1,2):
        P=rel(n,q,X,M); d,T=top(P,n)
        print('M=%d  ydeg=%d  #top=%d'%(M,d,len(T)))
        if len(T)<=40: print('   ',show(T,n))
