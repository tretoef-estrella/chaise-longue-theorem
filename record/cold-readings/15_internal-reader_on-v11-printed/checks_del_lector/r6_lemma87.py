# R6 (Grepy Tinta): Lemma 8.7. Uses the polynomial/Pfaffian functions of my r3 engine (definitions only).
import sys, itertools, time
import numpy as np
from collections import defaultdict
SRC=open('checks/r3_thm811_v3.py').read().split('# ---------- main ----------')[0]
def env(r):
    sys.argv=['x',str(r),'1','2']
    g={}
    exec(SRC,g)
    return g
t0=time.time()
def test(r,l,t,primes,wrongE=None):
    g=env(r); n=l+1+2*t; R=g['ring'](n)
    E=g['Eset'](l) if wrongE is None else wrongE
    PF=g['pf_bordered'](n,range(n),E)
    if not PF: return 'Pfaffian is zero'
    d0=sum(next(iter(PF)))
    gens=[]; firstS=None; gens_minus=[]
    for S in itertools.combinations(range(n),l+1):
        if firstS is None: firstS=S
        V=g['vander'](n,S); rest=[x for x in range(n) if x not in S]
        for Mt in g['perfect_matchings'](rest):
            P=V
            for (a,b) in Mt: P=g['pmul'](P,g['Dpoly'](n,a,b))
            if P:
                gens.append(P)
                if S!=firstS: gens_minus.append(P)
    out=[]
    for p in primes:
        def member(G):
            # graded ideal up to degree d0 only
            gd=defaultdict(list)
            for P in G:
                Pm={k:v%p for k,v in P.items() if v%p}
                if not Pm: continue
                d=sum(next(iter(Pm)))
                if d>d0: continue
                v=np.zeros(len(R.monos[d]),dtype=np.int64)
                for e,c in Pm.items(): v[R.pos[d][e]]=c
                gd[d].append(v)
            prev=None
            for d in range(d0+1):
                rows=list(gd.get(d,[]))
                if prev is not None and len(prev):
                    for j in range(n):
                        s_,d_=R.shift[(d-1,j)]
                        W=np.zeros((prev.shape[0],len(R.monos[d])),dtype=np.int64); W[:,d_]=prev[:,s_]; rows.extend(list(W))
                prev=g['rref'](np.array(rows,dtype=np.int64),p)[0] if rows else np.zeros((0,len(R.monos[d])),dtype=np.int64)
            v=np.zeros(len(R.monos[d0]),dtype=np.int64)
            for e,c in PF.items(): v[R.pos[d0][e]]=c%p
            if not v.any(): return 'Pf=0 mod p'
            rk0=prev.shape[0]
            rk1=g['rref'](np.vstack([prev,v[None,:]]),p)[0].shape[0]
            return rk1==rk0
        out.append((p,member(gens),member(gens_minus)))
    return out
primes=[2,3,5,7,10007]
print('columns: p, member of U_l(B_0), member after removing the generators of the first S (control)')
for (r,l,t) in [(3,0,1),(3,1,1),(3,0,2),(5,0,1),(5,1,1),(5,2,1),(5,0,2),(7,0,1),(7,1,1),(7,3,0),(9,0,1),(9,1,1)]:
    res=test(r,l,t,primes)
    print('(r,l,t)=(%d,%d,%d) n=%d :'%(r,l,t,l+1+2*t),res,'(%.1fs)'%(time.time()-t0)); sys.stdout.flush()
print('== P6.3 wrong borders (measured, no prediction) ==')
for (r,l,t,E) in [(5,2,1,[1]),(7,2,1,[3]),(5,0,1,[3]),(7,0,1,[5]),(5,0,1,[2]),(5,1,1,[0,1])]:
    try:
        res=test(r,l,t,[2,3,10007],wrongE=E)
    except Exception as ex:
        res='error: %r'%ex
    print('(r,l,t)=(%d,%d,%d) borders %s :'%(r,l,t,E),res); sys.stdout.flush()
print('time %.1fs'%(time.time()-t0))
