# Step 9: peripheral claims.  Each block prints its own prediction and result and flushes.
import sys, time, itertools
sys.path.insert(0,'checks')
from lib_chaise import *
mode=sys.argv[1]
if mode=="thm41":
    # Theorem 4.1: at q=3 the lex leading monomials (y_1>...>y_{n'}) of (D_J)C are exactly y_U, U in the ballot set; graded ranks C(n',u)-C(n',u+2).
    from math import comb
    for k in range(1,6):
        n1=2*k+1; N=2*k+2
        R=PolynomialRing(GF(3),n1,'y',order='lex'); y=R.gens()
        gens=[]
        for J in matchings(range(N)):
            g=R(1)
            for a,b in J:
                if a==0: continue
                g*=(y[b-1]-y[a-1])
            gens.append(g)
        I=R.ideal(gens+[v^2 for v in y])
        G=I.groebner_basis()
        LM=set(g.lm() for g in G)
        # standard monomials of I among squarefree monomials -> leading monomials of the IDEAL restricted to C = squarefree monomials not standard
        sqf=[e for e in itertools.product(range(2),repeat=n1)]
        def divisible(e): return any(all(e[i]>=l.exponents()[0][i] for i in range(n1)) for l in LM)
        lead={e for e in sqf if divisible(e)}
        ballot=set()
        for e in sqf:
            hgt=0; ok=True
            for i in range(n1):
                hgt+= 1 if e[i]==1 else -1
                if hgt<-1: ok=False;break
            if ok: ballot.add(e)
        ranks=[sum(1 for e in lead if sum(e)==u) for u in range(n1+1)]
        pred=[comb(n1,u)-comb(n1,u+2) if u>=k else 0 for u in range(n1+1)]
        print("Thm 4.1 k=%d: lead==ballot: %s ; |lead|=%d vs C(2k+2,k+1)=%d ; graded ranks %s vs predicted %s"%(k, lead==ballot, len(lead), comb(N,k+1), ranks[k:], pred[k:]), flush=True)
elif mode=="prop26":
    # Proposition 2.6: b_k(q-1) = dim F_p[y]/ intersection_J (I'_J + (y_i^{q-1})) equals dim (D_J)C.
    for (k,q,p) in [(1,3,3),(1,5,5),(2,3,3),(1,7,7),(2,5,5)]:
        m=2*k+1; N=2*k+2
        R=PolynomialRing(GF(p),m,'y'); y=R.gens()
        box=[v^(q-1) for v in y]
        Iint=None
        for J in matchings(range(N)):
            I=R.ideal([y[a-1]+y[b-1] for a,b in J if a!=0]+box)
            Iint=I if Iint is None else Iint.intersection(I)
        bk=Iint.vector_space_dimension()
        print("Prop 2.6 (k,q)=(%d,%d): b_k(q-1)=%d vs Q_k(q)=%d : %s"%(k,q,bk,Qk(k,q),"EQUAL" if bk==Qk(k,q) else "DIFFERENT"), flush=True)
elif mode=="thmA":
    # Theorem A at small cells and the char-2 numbers of Remark 6.3(1)
    from math import factorial as pyfact
    def Nq(n,q):
        h=(q-1)//2
        from fractions import Fraction
        I0=[Fraction(int(1),int(pyfact(j//2))**2) if j%2==0 else Fraction(int(0)) for j in range(n+1)]
        ey=[Fraction(int(1),int(pyfact(j))) for j in range(n+1)]
        def mul(A,B):
            C=[Fraction(int(0))]*(n+1)
            for i,a in enumerate(A):
                for j,b in enumerate(B):
                    if i+j<=n: C[i+j]+=a*b
            return C
        P=ey
        for _ in range(h): P=mul(P,I0)
        return int(P[n]*int(pyfact(n)))
    for (n,q,p) in [(2,3,3),(4,3,3),(4,5,5),(4,7,7),(6,3,3),(4,3,5),(4,5,3),(4,9,3),(6,5,5),(4,3,0),(4,5,0),(2,5,2),(4,3,2),(4,5,2),(4,7,2),(4,9,2)]:
        F=QQ if p==0 else GF(p)
        R=PolynomialRing(F,n,'x'); x=R.gens()
        E=[R(SymmetricFunctions(F).e()[j].expand(n)(x)) if False else sum(prod(c) for c in itertools.combinations(x,j)) for j in range(1,n+1,2)]
        I=R.ideal(E+[v^q for v in x])
        d=I.vector_space_dimension()
        print("Thm A n=%d q=%d char %s: dim=%d, N_q(n)=%d : %s"%(n,q,p if p else 0,d,Nq(n,q),"EQUAL" if d==Nq(n,q) else ("char 2 (fails as Remark 6.3 says)" if p==2 else "DIFFERENT")), flush=True)
elif mode=="fact72":
    # Fact 7.2: q=9, k=2, K = J minus {[[0,1],[2,3],[4,5]], [[0,2],[1,5],[3,4]]}: dim (D_J : J in K)C = 4730 < 4736 = |Gamma_K|.
    k,q,p=2,9,3; m=5; N=6
    Js=list(matchings(range(N)))
    norm=lambda J: sorted((min(a,b),max(a,b)) for a,b in J)
    ex1=[(0,1),(2,3),(4,5)]; ex2=[(0,2),(1,5),(3,4)]
    K=[J for J in Js if norm(J) not in (ex1,ex2)]
    assert len(K)==13
    # |Gamma_K| in mu_9\{1}
    cnt=0
    for a in itertools.product(range(1,9),repeat=m):
        if any(all((a[x-1]+a[y_-1])%9==0 for (x,y_) in J if x!=0) for J in K): cnt+=1
    print("Fact 7.2: |Gamma_K| =",cnt,"(paper 4736)", flush=True)
    R=PolynomialRing(GF(3),m,'y'); y=R.gens()
    D=lambda a,b: sum((-1)^u*y[a]^u*y[b]^(q-2-u) for u in range(q-1))
    gens=[]
    for J in K:
        g=R(1)
        for a,b in J:
            if a==0: continue
            g*=D(a-1,b-1)
        gens.append(g)
    t0=time.time()
    I=R.ideal(gens+[v^(q-1) for v in y]); vsd=I.vector_space_dimension()
    print("Fact 7.2: dim (D_J : J in K)C = %d (paper 4730); %s ; %.1fs"%(8^m-vsd, "deficit %d"%(cnt-(8^m-vsd)), time.time()-t0), flush=True)
elif mode=="cell":
    k,q,p=[int(x) for x in sys.argv[2].split(',')]
    m=2*k+1; N=2*k+2
    R=PolynomialRing(GF(p),m,'y'); y=R.gens()
    D=lambda a,b: sum((-1)^u*y[a]^u*y[b]^(q-2-u) for u in range(q-1))
    gens=[]
    for J in matchings(range(N)):
        g=R(1)
        for a,b in J:
            if a==0: continue
            g*=D(a-1,b-1)
        gens.append(g)
    t0=time.time()
    I=R.ideal(gens+[v^(q-1) for v in y]); vsd=I.vector_space_dimension()
    print("(k,q)=(%d,%d) over F_%d: dim (D_J)C = %d ; Q_k(q) = %d ; %s ; %.1fs"%(k,q,p,(q-1)^m-vsd,Qk(k,q),"EQUAL" if (q-1)^m-vsd==Qk(k,q) else "DIFFERENT",time.time()-t0), flush=True)
    if len(sys.argv)>3 and sys.argv[3]=="graded":
        # graded ranks via Hilbert function of the quotient
        hf=[]
        d0=k*(q-2); dmax=m*(q-2)
        Q=R.quotient(I)
        # use the standard monomials of a degree-compatible GB
        R2=PolynomialRing(GF(p),m,'y',order='degrevlex'); I2=R2.ideal([R2(g) for g in gens]+[v^(q-1) for v in R2.gens()])
        G=I2.groebner_basis(); LM=[g.lm().exponents()[0] for g in G]
        cnt_std={}
        for e in itertools.product(range(q-1),repeat=m):
            if not any(all(e[i]>=l[i] for i in range(m)) for l in LM): cnt_std[sum(e)]=cnt_std.get(sum(e),0)+1
        from math import comb
        tot={}
        for e in itertools.product(range(q-1),repeat=m): tot[sum(e)]=tot.get(sum(e),0)+1
        print("   graded ranks of the ideal from degree %d:"%d0,[tot[d]-cnt_std.get(d,0) for d in range(d0,dmax+1)], flush=True)
