# Step 8: dim V_Lambda vs |Z_Lambda| for EVERY down-set at several cells, in the "right" characteristic (Theorem 5.9 applies),
# in characteristics where Thm 5.9 applies but q is not a power of p, and in characteristics dividing q-1 (measured only).
# Also (P3) Proposition 5.8 as ideal membership: every generator of V_{Lambda_i} (on y_2..y_m) lies in W_{q-2-i}(V_Lambda),
# checked by linear algebra on the slices, at (5,3),(5,4),(7,3),(9,3),(9,4),(11,3).
# Prediction: dim V_Lambda = |Z_Lambda| whenever char does not divide q-1; >= always; P3: 0 failures.
# Estimate: largest ring (9,4)/(7,5)/(5,6): 4096-7776 dims; Singular vsd; whole script < 5 min, < 600 MB.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import *
def dimV(Lam,m,q,p):
    R=PolynomialRing(GF(p),m,'y'); y=R.gens()
    gens=[R(g) for g in V_generators(Lam,m,q)]
    I=R.ideal(gens+[v^(q-1) for v in y])
    return (q-1)^m - I.vector_space_dimension()
def check_P3(m,q,p):
    """for each down-set Lambda and each i: V_{Lambda_i} (built on indices 1..m-1) subset of W_{q-2-i}(V_Lambda), via slices:
       W_j(V) = { [y_0^j] f : f in V, deg_{y_0} f <= j }.  We compute W_j as a vector space: take all elements u*g of V (u monomial, g generator),
       restrict to those of y_0-degree <= j?  No: W_j needs all f in V with deg<=j, not only products.  We compute it exactly:
       V as a subspace of C_m (basis of monomials), then V_{<=j} = V ∩ span(monomials with y_0-exp <= j) by linear algebra, then project."""
    h=(q-1)//2; F=GF(p)
    monos=list(itertools.product(range(q-1),repeat=m)); col={e:i for i,e in enumerate(monos)}
    monos1=list(itertools.product(range(q-1),repeat=m-1)); col1={e:i for i,e in enumerate(monos1)}
    def span_of_ideal(gens, mvars, cols, monolist):
        rows=[]
        for g in gens:
            for u in monolist:
                r=[0]*len(cols)
                nz=False
                for e,c in g.items():
                    ee=tuple(x+y for x,y in zip(e,u))
                    if all(x<=q-2 for x in ee): r[cols[ee]]=(r[cols[ee]]+c)%p; nz=True
                if nz: rows.append(r)
        if not rows: return matrix(F,0,len(cols))
        return matrix(F,rows).echelon_form()
    P=Par(m,h); fails=0; tests=0; ctrl_fail=[0]; ctrl_tests=[0]
    for Lam in downsets(P):
        gens=V_generators(Lam,m,q)
        Vmat=span_of_ideal(gens,m,col,monos)
        Vmat=Vmat[:Vmat.rank()]
        Vspace=Vmat.row_space()
        Ls=layers(Lam,m,h,q)
        for i,L in enumerate(Ls):
            j=q-2-i
            # V_{<=j}: intersect V with the coordinate subspace of monomials with exponent of y_0 <= j
            allowed=[col[e] for e in monos if e[0]<=j]
            Sub=(F^len(monos)).subspace([ (F^len(monos)).gen(c) for c in allowed]) if allowed else (F^len(monos)).subspace([])
            Vle=Vspace.intersection(Sub)
            # project: coefficient of y_0^j
            Wrows=[]
            for v in Vle.basis():
                r=[0]*len(monos1)
                for e in monos:
                    if e[0]==j and v[col[e]]!=0: r[col1[e[1:]]]=v[col[e]]
                Wrows.append(r)
            W=(F^len(monos1)).subspace([vector(F,r) for r in Wrows]) if Wrows else (F^len(monos1)).subspace([])
            # generators of V_{Lambda_i} on indices 1..m-1 (as polys in m-1 variables)
            gi=V_generators(L,m-1,q)
            # negative control (Remark 5.10(2)): the slice one lower, W_{q-3-i}
            Wlow=None
            if j-1>=0:
                allowed2=[col[e] for e in monos if e[0]<=j-1]
                Sub2=(F^len(monos)).subspace([(F^len(monos)).gen(c) for c in allowed2]) if allowed2 else (F^len(monos)).subspace([])
                Vle2=Vspace.intersection(Sub2)
                W2rows=[]
                for v in Vle2.basis():
                    r=[0]*len(monos1)
                    for e in monos:
                        if e[0]==j-1 and v[col[e]]!=0: r[col1[e[1:]]]=v[col[e]]
                    W2rows.append(r)
                Wlow=(F^len(monos1)).subspace([vector(F,r) for r in W2rows]) if W2rows else (F^len(monos1)).subspace([])
            for g in gi:
                r=[0]*len(monos1)
                for e,c in g.items():
                    if all(x<=q-2 for x in e): r[col1[e]]=c%p
                tests+=1
                if vector(F,r) not in W: fails+=1; print("P3 FAIL",q,m,p,sorted(Lam),i,sorted(L),g)
                if Wlow is not None and vector(F,r)!=0 and vector(F,r) not in Wlow: ctrl_fail[0]+=1
                ctrl_tests[0]+=1
    print("P3 membership (q,m)=(%d,%d) over F_%d: down-sets=%d tests=%d FAILURES=%d ; negative control (slice q-3-i): %d of %d generators NOT in the lower slice (paper says the lower slice fails)"%(q,m,p,len(downsets(P)),tests,fails,ctrl_fail[0],ctrl_tests[0]), flush=True)
cells=[(5,2,5),(5,3,5),(5,4,5),(5,5,5),(7,2,7),(7,3,7),(7,4,7),(9,3,3),(9,4,3),(11,3,11),(13,3,13),(3,4,3),(3,5,3),(3,6,3),
       (5,3,3),(5,4,3),(5,4,7),(7,3,5),(7,3,11),(9,3,5),(9,4,7),(11,3,3),(13,3,5),
       (5,3,2),(5,4,2),(7,3,2),(7,3,3),(7,4,3),(7,4,2),(9,3,2),(9,4,2),(11,3,5),(11,3,2),(13,3,3),(13,3,2),(5,5,2),(5,6,3),(7,5,3)]
mode=sys.argv[1] if len(sys.argv)>1 else "dims"
if mode=="dims":
    for (q,m,p) in cells:
        h=(q-1)//2; P=Par(m,h); t0=time.time()
        res=[]; bad=0; strict=0
        for Lam in downsets(P):
            dv=dimV(Lam,m,q,p); z=sum(count_shape_formula(l,m,h) for l in Lam)
            res.append((dv,z))
            if dv<z: bad+=1
            if dv>z: strict+=1
        tag = "Thm5.9 applies" if (q-1)%p!=0 else "p | q-1 (no claim)"
        print("(q,m)=(%d,%d) over F_%d [%s]: down-sets=%d; dim<|Z| (would refute 5.3): %d; dim>|Z|: %d; dims=%s  [%.1fs]"%(q,m,p,tag,len(res),bad,strict,sorted(set(d for d,_ in res)) if len(res)<=12 else "...",time.time()-t0), flush=True)
        if strict: print("    strict cases:", [(sorted(L),dv,z) for L,(dv,z) in zip(downsets(P),res) if dv>z])
else:
    for (q,m,p) in [(5,3,5),(5,4,5),(7,3,7),(9,3,3),(3,4,3),(3,5,3),(9,4,3),(11,3,11)]:
        check_P3(m,q,p)
