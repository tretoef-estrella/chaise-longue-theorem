"""Step 5: the combinatorial skeleton of section 5, all down-sets, own code.
Checks, for each (q,m) and EVERY down-set Lambda of Par_m^{(h)}:
 P1  : for every tail M' in T^{m-1}, |F(M')| == F_Lambda(lambda(M'))  (brute force)
 Chain: options(mu) weakly increasing for <=;  options in Lambda form an initial segment
 (5.1): F = r + (q-1-2l)*iota + (l-j0+1)[j0 exists] with r,j0 as in the paper
 P2  : every layer Lambda_i is a down-set of Par_{m-1}^{(h)};  also opt_p(mu)<=opt_p(mu~) for all comparable pairs
 5.8 : the cases (alpha),(beta),(gamma) are exhaustive and exclusive when F>=1, and the slice q-1-F equals j0-1 / l / q-1-r
 Peel: |Z_Lambda| == sum_i |Z_{Lambda_i}| (Lemma 5.1(iv) + P1), with |Z| by the class-formula and by brute force
Prediction: 0 failures.  Time: < 2 min total; memory < 200 MB."""
import sys, time; sys.path.insert(0,'checks')
from lib_chaise import *
from itertools import product
from collections import Counter
t0=time.time()
def first_last_rows(mu):
    l=len(mu)
    rbar=[max(j for j in range(l) if mu[j]==mu[i]) for i in range(l)]   # last row of that length (0-based)
    rlow=[min(j for j in range(l) if mu[j]==mu[i]) for i in range(l)]
    return rlow, rbar
tot_fail=0; tot_tests=0
for (q,m) in [(3,4),(3,6),(5,3),(5,4),(5,5),(5,6),(7,3),(7,4),(7,5),(9,3),(9,4),(9,5),(11,3),(11,4),(13,4)]:
    h=(q-1)//2; P=Par(m,h); P1=Par(m-1,h); Ds=downsets(P)
    brute = (q-1)**(m-1) <= 300000
    tails = list(product(range(q-1),repeat=m-1)) if brute else None
    tailshape = {M:residue_partition(M,h) for M in tails} if brute else None
    fails=0; tests=0
    # chain lemma and P2 on comparable pairs (independent of Lambda)
    for mu in P1:
        o=options(mu,h,q)
        assert len(o)==q-1
        for a,b in zip(o,o[1:]):
            tests+=1
            if not leq(a,b): fails+=1; print("CHAIN FAIL",q,m,mu,a,b)
        for x in o:
            if x not in P: fails+=1; print("OPTION NOT IN Par_m",q,m,mu,x)
    for mu in P1:
        for mut in P1:
            if leq(mu,mut):
                o1=options(mu,h,q); o2=options(mut,h,q)
                for a,b in zip(o1,o2):
                    tests+=1
                    if not leq(a,b): fails+=1; print("P2 FAIL",q,m,mu,mut,a,b)
    for Lam in Ds:
        Lset=set(Lam)
        Ls=layers(Lam,m,h,q)
        for i,L in enumerate(Ls):
            tests+=1
            if not is_downset(L,P1): fails+=1; print("LAYER NOT DOWNSET",q,m,sorted(Lam),i,sorted(L))
        # peel identity with class formula
        lhs=sum(count_shape_formula(l,m,h) for l in Lam)
        rhs=sum(sum(count_shape_formula(l,m-1,h) for l in L) for L in Ls)
        tests+=1
        if lhs!=rhs: fails+=1; print("PEEL FAIL",q,m,sorted(Lam),lhs,rhs)
        for mu in P1:
            o=options(mu,h,q); l=len(mu)
            F=F_Lambda(mu,Lam,h,q)
            inL=[x in Lset for x in o]
            tests+=1
            if inL!=sorted(inL,reverse=True): fails+=1; print("NOT INITIAL SEGMENT",q,m,sorted(Lam),mu,inL)
            # (5.1)
            rlow,rbar=first_last_rows(mu)
            r=sum(1 for j in range(l) if o[j] in Lset)
            iota=1 if (l<h and sort_part(mu+(1,)) in Lset) else 0
            adds=[j for j in range(l) if sort_part(mu[:j]+(mu[j]+1,)+mu[j+1:]) in Lset]
            j0=min(adds) if adds else None
            F51=r+(q-1-2*l)*iota+((l-j0) if j0 is not None else 0)
            tests+=1
            if F51!=F: fails+=1; print("(5.1) FAIL",q,m,sorted(Lam),mu,F,F51)
            if r>0 and rbar[r-1]!=r-1: fails+=1; print("r not last row of its length",q,m,mu,r)
            if j0 is not None and rlow[j0]!=j0: fails+=1; print("j0 not first row",q,m,mu,j0)
            if F>=1:
                cases=[j0 is not None, (j0 is None and iota==1), (j0 is None and iota==0)]
                if sum(cases)!=1: fails+=1; print("CASES not exclusive",q,m,sorted(Lam),mu)
                if j0 is not None: slice_=j0  # j0 is 0-based here: paper's j0-1
                elif iota==1: slice_=l
                else: slice_=q-1-r
                tests+=1
                if slice_!=q-1-F: fails+=1; print("SLICE FAIL",q,m,sorted(Lam),mu,slice_,q-1-F)
                if j0 is not None and r!=l: fails+=1; print("alpha but r!=l",q,m,mu)
                if iota==1 and r!=l: fails+=1; print("iota but r!=l",q,m,mu)
        if brute:
            # P1 by brute force
            fib=Counter()
            for M in tails:
                sh=tailshape[M]
                fib[M]=sum(1 for y in range(q-1) if residue_partition((y,)+M,h) in Lset)
            for M in tails:
                tests+=1
                if fib[M]!=F_Lambda(tailshape[M],Lam,h,q): fails+=1; print("P1 FAIL",q,m,sorted(Lam),M)
            # |Z_{>i}| = |Z_{Lambda_i}|
            for i,L in enumerate(Ls):
                tests+=1
                if sum(1 for M in tails if fib[M]>i)!=sum(1 for M in tails if tailshape[M] in L): fails+=1; print("Z>i FAIL",q,m,i)
    print("(q,m)=(%d,%d): |Par_m|=%d, #downsets=%d, brute=%s, tests=%d, FAILURES=%d  [%.1fs]"%(q,m,len(P),len(Ds),brute,tests,fails,time.time()-t0), flush=True)
    tot_fail+=fails; tot_tests+=tests
# P2 with large h on random comparable pairs (long, uneven partitions; lengths hitting the cap)
import random
random.seed(1)
fails=0;tests=0
for trial in range(20000):
    h=random.choice([1,2,3,4,6,13,40,60]); q=2*h+1
    m1=random.randint(1,14)
    # random partitions of size <= m1 with same parity as m1 and length <= h
    def rp():
        s=random.choice(range(m1%2, m1+1,2))
        while True:
            lam=tuple(sorted([random.randint(1,max(1,s)) for _ in range(random.randint(0,min(h,s) if s>0 else 0))],reverse=True))
            if sum(lam)<=s and (s-sum(lam))%2==0 and len(lam)<=h: 
                # pad to exact size s by adding to parts / new parts of length 1
                lam=list(lam)
                while sum(lam)<s:
                    if lam and random.random()<0.7: lam[random.randrange(len(lam))]+=1
                    elif len(lam)<h: lam.append(1)
                    else: lam[random.randrange(len(lam))]+=1
                return sort_part(lam)
    mu=rp(); mut=rp()
    if leq(mu,mut) and sum(mu)%2==sum(mut)%2:
        o1=options(mu,h,q); o2=options(mut,h,q)
        for a,b in zip(o1,o2):
            tests+=1
            if not leq(a,b): fails+=1; print("P2 RANDOM FAIL",h,mu,mut,a,b)
print("P2 random large-h pairs: tests=%d FAILURES=%d"%(tests,fails))
tot_fail+=fails
print("TOTAL tests=%d FAILURES=%d elapsed %.1fs"%(tot_tests+tests,tot_fail,time.time()-t0))
