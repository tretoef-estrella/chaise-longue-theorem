# Gate for Main Theorem′ at primes p ∤ m and p | m, k = 1, literal ring F_p[t1,t2,t3]/(t_i^m - 1).
import itertools, sys
def rank_mod(rows, p, ncols):
    piv={}; r=0
    for v in rows:
        v=v[:]
        for c in range(ncols):
            if v[c]%p==0: continue
            if c in piv:
                pv=piv[c]; f=v[c]*pow(pv[c],p-2,p)%p
                v=[(a-f*b)%p for a,b in zip(v,pv)]
            else:
                piv[c]=v; r+=1; break
    return r
def run(m,p):
    idx={e:i for i,e in enumerate(itertools.product(range(m),repeat=3))}
    def mono(e,c=1): return {tuple(x%m for x in e):c}
    def mul(a,b):
        out={}
        for e1,c1 in a.items():
            for e2,c2 in b.items():
                e=tuple((x+y)%m for x,y in zip(e1,e2)); out[e]=(out.get(e,0)+c1*c2)%p
        return out
    def tminus1(i): e=[0,0,0]; e[i]=1; return {tuple(e):1,(0,0,0):p-1}
    def phi(i,j):
        out={}
        for a in range(m):
            e=[0,0,0]; e[i]+=a; e[j]+=a; e=tuple(x%m for x in e); out[e]=(out.get(e,0)+1)%p
        return out
    # J = [[0,k0],[j1,k1]] with indices 1..3 -> positions 0..2
    Js=[(1,(2,3)),(2,(1,3)),(3,(1,2))]
    gens=[]
    for k0,(j1,k1) in Js:
        g=mul(mul(tminus1(k0-1),tminus1(k1-1)),phi(j1-1,k1-1)); gens.append(g)
    rows=[]
    for g in gens:
        for e in idx:
            h=mul(g,mono(e)); v=[0]*len(idx)
            for ee,c in h.items(): v[idx[ee]]=c
            rows.append(v)
    r=rank_mod(rows,p,len(idx))
    Q=3*(m-1)*(m-2)
    print(f"m={m} p={p}: dim quotient = {m**3-r}, predicted m^3-Q_1(m) = {m**3-Q}  {'OK' if r==Q else 'FAIL'}")
for m,p in [(3,2),(3,3),(3,5),(5,2),(5,3),(5,5),(5,7),(7,2),(7,3),(7,7),(9,2),(9,3)]:
    run(m,p)
