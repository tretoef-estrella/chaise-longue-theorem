# Step 6: the two ingredients of Theorem 5.9, on every point.
# (i) Evaluation: on T = mu_{q-1} inside a field of char p not dividing q-1, D(a,b)=0 unless b=-a, and D(a,-a) = -(q-1) a^{q-2} != 0.
#     Also: when p | q-1 (q=7,p=3; q=5,p=2; q=13,p=3) D(a,-a) = 0 on F_q^x-like sets? (we use T = the (q-1)-th roots of unity in an extension when they exist)
# (ii) Support: for every M in T^m and every tight pattern of every lambda in Par_m^{(h)}: product(M) != 0  ==>  lambda(M) <= lambda;
#      and the pattern built from M (nu(M) negation pairs + residue in the columns of lambda(M)) is non-zero at M  (the parenthetical claim Sigma = Z_Lambda).
# Prediction: 0 failures.  Cells (q,m) = (5,3),(5,4),(7,3),(7,4),(9,3),(9,4) with T = F_q^x (q=9: GF(9)).  < 2 min, < 300 MB.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import Par, leq, tight_patterns, residue_partition, nu, conjugate, sort_part
def Dval(a,b,q): return sum((-1)^u * a^u * b^(q-2-u) for u in range(q-1))
def Delta(vals):
    r=1
    for i in range(len(vals)):
        for j in range(i+1,len(vals)): r*= (vals[j]-vals[i])
    return r
for (q,m) in [(5,3),(5,4),(7,3),(7,4),(9,3),(9,4),(11,3),(13,3)]:
    F=GF(q,'w'); h=(q-1)//2
    T=[x for x in F if x!=0]
    # order T as u_0,-u_0,u_1,-u_1,... so that index u//2 = class, u^1 = negation
    Tl=[]; seen=set()
    for x in T:
        if x in seen: continue
        Tl+= [x,-x]; seen|={x,-x}
    assert len(Tl)==q-1
    # (i)
    bad=0
    for a in Tl:
        for b in Tl:
            v=Dval(a,b,q)
            if b==-a:
                if v!= -(q-1)*a^(q-2) or v==0: bad+=1
            else:
                if v!=0: bad+=1
    print("(q,m)=(%d,%d) evaluation of D on TxT: failures=%d"%(q,m,bad), flush=True)
    # (ii)
    P=Par(m,h)
    pats={lam:list(tight_patterns(lam,list(range(m)))) for lam in P}
    fails=0; tests=0; t0=time.time()
    for Midx in itertools.product(range(q-1),repeat=m):
        M=[Tl[i] for i in Midx]; lamM=residue_partition(Midx,h)
        for lam in P:
            for pairs,blocks in pats[lam]:
                val=1
                for a,b in pairs:
                    val*=Dval(M[a],M[b],q)
                    if val==0: break
                if val!=0:
                    for B in blocks:
                        val*=Delta([M[i] for i in B])
                        if val==0: break
                tests+=1
                if val!=0 and not leq(lamM,lam): fails+=1; print("SUPPORT FAIL",q,m,Midx,lam,pairs,blocks)
        # pattern of lambda(M) non-zero at M
        cnt={}
        for i,u in enumerate(Midx): cnt.setdefault(u//2,[[],[]])[u%2].append(i)
        pairs=[]; rows=[]
        for c,(A,B) in cnt.items():
            k_=min(len(A),len(B)); pairs+=list(zip(A[:k_],B[:k_]))
            maj=A[k_:] if len(A)>len(B) else B[k_:]
            if maj: rows.append(maj)
        rows.sort(key=len,reverse=True)
        lam=tuple(len(r) for r in rows); assert lam==lamM
        blocks=[[r[c] for r in rows if len(r)>c] for c in range(lam[0] if lam else 0)]
        val=1
        for a,b in pairs: val*=Dval(M[a],M[b],q)
        for B in blocks: val*=Delta([M[i] for i in B])
        tests+=1
        if val==0: fails+=1; print("SIGMA=Z FAIL",q,m,Midx)
    print("(q,m)=(%d,%d) support statement on all %d points x all patterns: tests=%d failures=%d  [%.1fs]"%(q,m,(q-1)^m,tests,fails,time.time()-t0), flush=True)
# where p | q-1: D(a,-a) vanishes identically
for (q,p) in [(7,3),(5,2),(13,3),(7,2),(9,2)]:
    R=PolynomialRing(GF(p),'a'); a=R.gen()
    print("q=%d, char %d: D(a,-a) = %s  (zero polynomial: %s)"%(q,p,Dval(a,-a,q), Dval(a,-a,q)==0))
