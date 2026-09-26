# grepy_polys.py — the auditor's tiny exact polynomial engine (dict {exponent tuple: integer}), over ZZ, no Groebner.
# add, mul, mono, sc, e_ (elementary symmetric), h2 (h_D(-x_a, x_b)), Ssum (S^a_M(P)), phi (boson family), inbox, layer_ok.
# Used by the auditor to re-check INFORME_11 (Lemma G, Theorems A, B, E) and the three-letter identities of MISSION_12 §3.4.
import itertools, sys, time
from math import comb
T0=time.time()
def add(P,Q,c=1):
    R=dict(P)
    for m,v in Q.items():
        R[m]=R.get(m,0)+c*v
        if R[m]==0: del R[m]
    return R
def mul(P,Q):
    R={}
    for m1,v1 in P.items():
        for m2,v2 in Q.items():
            m=tuple(a+b for a,b in zip(m1,m2)); R[m]=R.get(m,0)+v1*v2
    return {m:v for m,v in R.items() if v}
def mono(nv,exps):
    e=[0]*nv
    for i,k in exps.items(): e[i]+=k
    return {tuple(e):1}
def sc(P,c): return {m:c*v for m,v in P.items() if c*v}
def e_(nv,S,k):
    if k<0 or k>len(S): return {}
    if k==0: return {tuple([0]*nv):1}
    R={}
    for T in itertools.combinations(S,k):
        e=[0]*nv
        for i in T: e[i]=1
        R[tuple(e)]=1
    return R
def h2(nv,a,b,D,sa=-1):  # h_D(sa*x_a, x_b)
    if D<0: return {}
    R={}
    for i in range(D+1):
        e=[0]*nv; e[a]+=i; e[b]+=D-i; R[tuple(e)]=R.get(tuple(e),0)+sa**i
    return R
def Ssum(nv,a,P,M):  # S^a_M(P) = sum_p a^{M-p} e_p(P)
    R={}
    for p in range(0,min(M,len(P))+1):
        R=add(R,mul(mono(nv,{a:M-p}),e_(nv,P,p)))
    return R
def mod3(P): return {m:v%3 for m,v in P.items() if v%3}
def inbox(m,q): return any(x>=q for x in m)
def boxred(P,q): return {m:v for m,v in P.items() if not inbox(m,q)}
def phi(nv,ys,q,ell,t,j,l):  # boson family y_j^{q-ell} sum_{i<ell} y_j^i e_{t-i}(y\{j,l})
    Pv=[i for i in ys if i!=j and i!=l]; R={}
    for i in range(ell): R=add(R,mul(mono(nv,{j:q-ell+i}),e_(nv,Pv,t-i)))
    return R
def layer_ok(m,w,q,vars_):
    # is monomial m (restricted to vars_) divisible by a generator x_A^{q-1} x_C with B nonempty, |B|-|A|<=w ?
    A=[i for i in vars_ if m[i]>=q-1]; sup=[i for i in vars_ if m[i]>=1]; Z=[i for i in vars_ if m[i]==0]
    if Z: return len(Z)-len(A)<=w
    C=[i for i in sup if i not in A]
    if C: return 1-len(A)<=w
    return 2-len(A)<=w
