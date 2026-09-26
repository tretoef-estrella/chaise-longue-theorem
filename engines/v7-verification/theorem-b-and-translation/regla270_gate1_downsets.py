# Gate 1 (combinatorial, structurally independent): ALL down-sets Lambda of Par_m.
# N_m(lam) by a class-by-class EGF DP (not by fibres). Checks:
#  P2: Lambda_i down-set; P1: |Z_Lam| == sum_i |Z_{Lam_i}|; P3: best construction slice <= q-1-F.
import sys, itertools
from fractions import Fraction
from math import factorial
def S(l,t): return sum(l[:t])
def leq(a,b):
    L=max(len(a),len(b),1)
    return all(S(a,t)<=S(b,t) for t in range(1,L+1))
def parts(n,maxpart=None):
    if maxpart is None: maxpart=n
    if n==0: yield (); return
    for p in range(min(n,maxpart),0,-1):
        for r in parts(n-p,p): yield (p,)+r
def Par(m,h): return [l for n in range(m%2,m+1,2) for l in parts(n) if len(l)<=h]
def canon(l): return tuple(sorted([x for x in l if x>0],reverse=True))
def options(mu,q,h):
    ell=len(mu); ops=[]
    for c in range(h):
        if c<ell:
            ops.append(canon(mu[:c]+(mu[c]-1,)+mu[c+1:])); ops.append(canon(mu[:c]+(mu[c]+1,)+mu[c+1:]))
        else:
            ops.append(canon(mu+(1,))); ops.append(canon(mu+(1,)))
    return ops  # q-1 = 2h options
NC={}
def Ncount(m,h):
    if (m,h) in NC: return NC[(m,h)]
    # DP over h classes: state (n, residue multiset) -> sum of 1/(a! abar!)
    st={(0,()):Fraction(1)}
    for _ in range(h):
        new={}
        for (n,res),w in st.items():
            for a in range(m-n+1):
                for ab in range(m-n-a+1):
                    r=abs(a-ab); key=(n+a+ab, canon(res+((r,) if r else ())))
                    new[key]=new.get(key,0)+w/Fraction(factorial(a)*factorial(ab))
        st=new
    out={}
    for (n,res),w in st.items():
        if n==m: out[res]=int(w*factorial(m))
    NC[(m,h)]=out; return out
def downsets(P,limit):
    P=sorted(P,key=lambda l:(sum(S(l,t) for t in range(1,len(P)+2)),l))
    below=[[j for j in range(i) if leq(P[j],P[i]) and P[j]!=P[i]] for i in range(len(P))]
    out=[]; cur=[False]*len(P)
    def rec(i):
        if len(out)>=limit: return
        if i==len(P): out.append(frozenset(P[j] for j in range(len(P)) if cur[j])); return
        cur[i]=False; rec(i+1)
        if all(cur[j] for j in below[i]):
            cur[i]=True; rec(i+1); cur[i]=False
    rec(0); return out
def rows_first(mu,j): # first row (1-based) with length mu[j-1]
    return min(i+1 for i in range(len(mu)) if mu[i]==mu[j-1])
def rows_last(mu,j):
    return max(i+1 for i in range(len(mu)) if mu[i]==mu[j-1])
q=int(sys.argv[1]); m=int(sys.argv[2]); limit=int(sys.argv[3]) if len(sys.argv)>3 else 10**6
h=(q-1)//2
Pm=Par(m,h); Pm1=Par(m-1,h)
Nm=Ncount(m,h); Nm1=Ncount(m-1,h)
assert sum(Nm.values())==(q-1)**m, "N count total"
DS=downsets(Pm,limit)
bad2=bad1=bad3=0
for Lam in DS:
    F={mu:sum(1 for o in options(mu,q,h) if o in Lam) for mu in Pm1}
    ZL=sum(Nm.get(l,0) for l in Lam)
    tot=0
    for i in range(q-1):
        Li=[mu for mu in Pm1 if F[mu]>i]
        tot+=sum(Nm1.get(mu,0) for mu in Li)
        Ls=set(Li)
        for a in Pm1:
            if a in Ls: continue
            if any(leq(a,b) for b in Li): bad2+=1; break
    if tot!=ZL: bad1+=1
    for mu in Pm1:
        f=F[mu]
        if f==0: continue
        ell=len(mu); cands=[]
        for j in range(1,ell+1):
            if canon(mu[:j-1]+(mu[j-1]+1,)+mu[j:]) in Lam: cands.append(rows_first(mu,j)-1)   # alpha
            if canon(mu[:j-1]+(mu[j-1]-1,)+mu[j:]) in Lam: cands.append(q-1-rows_last(mu,j))  # gamma
        if ell<h and canon(mu+(1,)) in Lam: cands.append(ell)                                 # beta
        if min(cands)>q-1-f: bad3+=1
print(f"q={q} m={m} |Par_m|={len(Pm)} downsets={len(DS)}{' (LIMIT)' if len(DS)>=limit else ''} P1fail={bad1} P2fail={bad2} P3fail={bad3}")
