# Step 7: the literal form of [DS] and the integer test of the whole translation.
# (a) dim_{F_p} F_p[t_1..t_{2k+1}]/(t_i^q - 1, psi_J) with psi_J exactly as in [DS] (tau_J * prod phi(t_j t_k)); prediction q^{2k+1} - Q_k(q).
# (b) Smith normal form over Z of A_K = R/(psi_J : J in J) at small cells: prediction rank = q^{2k+1}-Q_k(q), NO torsion (Main Theorem via Thm 0(a)).
# (c) positive control: subfamilies K at (k,q)=(2,3) with dim_{F_3}(D_J: J in K)C < |Gamma_K| (paper section 7.2 says 800 of 32767); take one and
#     compute the Smith form of A_K over Z: prediction: 3-torsion appears, of the predicted number of cyclic factors.
# Estimate: (b) largest matrix 2187 x 729 over Z ((1,9)) and 729 x 243 ((2,3)); < 2 min; < 500 MB.  (c) 32767 ranks of <=  (15*32) x 32 matrices over GF(3): ~1 min.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import Qk, matchings
def psi_list(k,q,R):
    t=R.gens(); N=2*k+2
    phi=lambda u: sum(u^i for i in range(q))
    out=[]
    for J in matchings(range(N)):
        J=[(min(a,b),max(a,b)) for a,b in J]
        g=R(1)
        for (a,b) in J:
            g*= (t[b-1]-1)          # tau_J: (t_{k_i}-1) for every pair, k_i = larger index (j_0 = 0 pair contributes t_{k_0}-1)
            if a>0: g*= phi(t[a-1]*t[b-1])
        out.append(g)
    return out
def literal_dim(k,q,p):
    m=2*k+1; R=PolynomialRing(GF(p),m,'t'); t=R.gens()
    I=R.ideal(psi_list(k,q,R)+[v^q-1 for v in t])
    vsd=I.vector_space_dimension()
    print("(a) literal [DS] form (k,q)=(%d,%d) over F_%d: dim F_p[G]/(psi_J) = %d ; q^{2k+1}-Q_k(q) = %d ; %s"%(k,q,p,vsd,q^m-Qk(k,q),"EQUAL" if vsd==q^m-Qk(k,q) else "DIFFERENT"), flush=True)
def snf(k,q,Ksel=None,label=""):
    m=2*k+1; R=PolynomialRing(ZZ,m,'t'); t=R.gens()
    psis=psi_list(k,q,R)
    if Ksel is not None: psis=[psis[i] for i in Ksel]
    exps=list(itertools.product(range(q),repeat=m)); col={e:i for i,e in enumerate(exps)}
    def reduce_exp(e): return tuple(x%q for x in e)
    rows=[]
    for g in psis:
        gd=g.dict()
        for u in exps:
            r=[0]*len(exps)
            for e,c in gd.items():
                ee=reduce_exp(tuple(x+y for x,y in zip(e,u)))
                r[col[ee]]+=int(c)
            rows.append(r)
    t0=time.time()
    M=matrix(ZZ,rows)
    ed=M.elementary_divisors()
    nz=[d for d in ed if d!=0]
    rank=len(nz); tors=[d for d in nz if d not in (1,-1)]
    print("(b%s) Z-Smith form (k,q)=(%d,%d)%s: rank(ideal)=%d, so rank A_K = %d (prediction %d); torsion invariants of A_K: %s ; %.1fs"%(label,k,q,(" K=%s"%Ksel if Ksel is not None else ""),rank,q^m-rank, (q^m-Qk(k,q)) if Ksel is None else -1, tors if tors else "NONE", time.time()-t0), flush=True)
    return tors
for (k,q,p) in [(1,3,3),(1,5,5),(1,7,7),(2,3,3),(1,9,3),(2,5,5),(1,11,11)]: literal_dim(k,q,p)
for (k,q) in [(1,3),(1,5),(1,7),(2,3),(1,9)]: snf(k,q)
# (c) positive control at (2,3): scan all subfamilies for the y-form deficit
k,q,p=2,3,3; m=5; N=6
Js=list(matchings(range(N)))
R=PolynomialRing(GF(3),m,'y'); y=R.gens()
D=lambda a,b: y[b]-y[a]
DJ=[]
for J in Js:
    g=R(1)
    for (a,b) in J:
        if a==0: continue
        g*=D(a-1,b-1)
    DJ.append(g)
monos=[e for e in itertools.product(range(2),repeat=m)]
col={e:i for i,e in enumerate(monos)}
vecs=[]
for g in DJ:
    vs=[]
    for u in monos:
        r=[0]*32
        for e,c in g.dict().items():
            ee=tuple(x+y_ for x,y_ in zip(e,u))
            if all(x<=1 for x in ee): r[col[ee]]=(r[col[ee]]+int(c))%3
        vs.append(r)
    vecs.append(vs)
# |Gamma_K| by enumeration in mu_3\{1} = exponents {1,2}
def GammaK(K):
    cnt=0
    for a in itertools.product([1,2],repeat=m):
        ok=False
        for i in K:
            if all(((a[x-1]+a[yy-1])%3==0) for (x,yy) in Js[i] if x!=0): ok=True;break
        cnt+=ok
    return cnt
GK={}
t0=time.time(); fails=[]; nonempty=0; worst=0
for mask in range(1,1<<15):
    K=[i for i in range(15) if mask>>i&1]
    rows=[r for i in K for r in vecs[i]]
    rk=matrix(GF(3),rows).rank()
    gk=GammaK(K)
    if rk>gk: print("!!! dim > |Gamma_K| for K=",K)
    if rk<gk: fails.append((K,rk,gk)); worst=max(worst,gk-rk)
print("(c) (k,q)=(2,3): subfamilies with dim(D_J:K)C < |Gamma_K|: %d of 32767 (paper: 800); worst deficit %d (paper: 2); %.1fs"%(len(fails),worst,time.time()-t0), flush=True)
ex=[f for f in fails if f[3-1]-f[1]==2][0] if any(f[2]-f[1]==2 for f in fails) else fails[0]
print("    example:",ex)
tors=snf(2,3,Ksel=ex[0],label="-control")
print("    prediction from Prop 2.1: number of cyclic 3-factors = deficit =",ex[2]-ex[1],"; found:",len(tors), "->", "CONSISTENT" if len(tors)==ex[2]-ex[1] and all(d%3==0 for d in tors) else "INCONSISTENT")
