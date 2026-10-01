# generacion.py -- Grepy, 1 Oct 2026.
# Test of the GENERATION statement:  sum_J D_J * B  =  ann_B(e_odd)   (n even),
# B = F_p[x_1..x_n]/(x_i^q),  D(a,b) = sum_j (-1)^j x_a^j x_b^(q-1-j)  (the invariant copairing),
# D_J = product of D(a,b) over the pairs of the perfect matching J.
# Lie reading: the invariants of the regular unipotent centralizer of SO_q (q odd) / Sp_q (q even)
# in V^{(x)n} are generated, over the algebra of the n commuting copies of e, by the G-invariants (Brauer matchings).
# We compute dim sum_J D_J B and compare with N = number of closed n-walks on Z^m (with loops iff q odd).
# Estimate (largest cell (5,6)): 15*125 vectors of length 15625, rank 1001 -> < 200 MB, < 1 min.
import sys, itertools, numpy as np
def matchings(pts):
    if not pts: yield []; return
    a=pts[0]
    for i in range(1,len(pts)):
        b=pts[i]; rest=pts[1:i]+pts[i+1:]
        for M in matchings(rest): yield [(a,b)]+M
def walks(q,n):
    m=q//2; loop=q%2
    from collections import Counter
    cur=Counter({(0,)*m:1})
    for _ in range(n):
        nx=Counter()
        for p,c in cur.items():
            if loop: nx[p]+=c
            for i in range(m):
                for s in (1,-1):
                    r=list(p); r[i]+=s; nx[tuple(r)]+=c
        cur=nx
    return cur[(0,)*m]
def run(q,n,p):
    N=q**n
    def idx(e):
        r=0
        for t in e: r=r*q+t
        return r
    basis=np.zeros((0,N),dtype=np.int64); piv=[]
    rank=0
    for J in matchings(list(range(n))):
        # D_J as dict exponent->coef
        poly={(0,)*n:1}
        for (a,b) in J:
            new={}
            for e,c in poly.items():
                for j in range(q):
                    f=list(e); f[a]+=j; f[b]+=q-1-j
                    new[tuple(f)]=(new.get(tuple(f),0)+c*(-1)**j)%p
            poly=new
        firsts=[a for a,b in J]
        vecs=[]
        for mult in itertools.product(range(q),repeat=len(J)):
            v=np.zeros(N,dtype=np.int64); ok=False
            for e,c in poly.items():
                f=list(e)
                for a,t in zip(firsts,mult): f[a]+=t
                if max(f)<q:
                    v[idx(f)]=(v[idx(f)]+c)%p; ok=True
            if ok: vecs.append(v)
        for v in vecs:
            if rank:
                coef=v[piv]%p
                v=(v-coef@basis)%p
            nz=np.nonzero(v)[0]
            if len(nz)==0: continue
            k=nz[0]; inv=pow(int(v[k]),p-2,p); v=(v*inv)%p
            if rank:
                col=basis[:,k].copy()
                basis=(basis-np.outer(col,v))%p
            basis=np.vstack([basis,v]); piv.append(k); rank+=1
    return rank
cells=[(3,2),(3,4),(3,6),(5,2),(5,4),(7,4),(9,4),(5,6),(2,4),(2,6),(4,4),(4,6),(6,4)]
primes=[3,5,7,32003]
ok=tot=0
for (q,n) in cells:
    Nw=walks(q,n)
    for p in primes:
        if (q,n)==(5,6) and p not in (3,5): continue
        r=run(q,n,p); tot+=1; ok+= (r==Nw)
        print(f"q={q} n={n} p={p}: dim sum_J D_J B = {r}   walks = {Nw}   {'OK' if r==Nw else 'DIFFERENT'}",flush=True)
print(f"TOTAL {ok}/{tot}")
