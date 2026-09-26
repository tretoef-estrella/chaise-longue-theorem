"""Step 3 of the audit: the counts. Prediction: table of section 3 reproduced; Q_2, Q_3 polynomials; Lemma 2.2 / Lemma 3.1 bijections
by brute force at small cells; section 5.10 numbers. Time < 30 s, memory < 100 MB."""
import sys, time; sys.path.insert(0,'checks')
from lib_chaise import *
from itertools import product
t0=time.time()
print("== Q_k(q) table (paper section 3) ==")
for q in [3,5,7,9,11,13,25,27]:
    print(q, [Qk(k,q) for k in range(1,6)])
print("Q_1(q)=3(q-1)(q-2):", all(Qk(1,q)==3*(q-1)*(q-2) for q in range(3,40,2)))
print("Q_2(q) poly:", all(Qk(2,q)==15*q**3-90*q**2+175*q-100 for q in range(3,40,2)))
print("Q_3(q) poly:", all(Qk(3,q)==105*q**4-1050*q**3+3955*q**2-6335*q+3325 for q in range(3,40,2)))
from math import comb
print("Q_k(3)=C(2k+2,k+1):", all(Qk(k,3)==comb(2*k+2,k+1) for k in range(0,10)))
print("== Lemma 2.2: |Gamma_J| in mu_q\\{1} by brute force vs Q_k(q) ==")
def Gamma_count(k,q):
    n1=2*k+1; N=2*k+2
    Js=[]
    for M in matchings(range(N)):
        Js.append(M)
    cnt=0
    for a in product(range(1,q), repeat=n1):  # exponents of zeta, a_i != 1 means exponent != 0
        ok=False
        for J in Js:
            good=True
            for (x,y) in J:
                if 0 in (x,y): continue
                if (a[x-1]+a[y-1])%q!=0: good=False;break
            if good: ok=True;break
        cnt+=ok
    return cnt
for (k,q) in [(1,3),(1,5),(1,7),(2,3),(2,5),(1,9)]:
    print((k,q), Gamma_count(k,q), Qk(k,q))
print("== Lemma 3.1: |Gamma'| = #{y in T^{2k+1}: nu(y)=k} ==")
for (k,q) in [(1,3),(1,5),(1,7),(2,3),(2,5),(3,3),(1,9),(2,7)]:
    h=(q-1)//2; m=2*k+1
    c=sum(1 for M in product(range(q-1),repeat=m) if nu(M,h)==k)
    c2=sum(1 for M in product(range(q-1),repeat=m) if residue_partition(M,h)==(1,))
    print((k,q), c, c2, Qk(k,q))
print("== count_shape_formula vs brute force, several cells ==")
bad=0
for (q,m) in [(3,4),(5,3),(5,4),(7,3),(7,4),(9,3),(9,4),(5,5)]:
    h=(q-1)//2
    from collections import Counter
    C=Counter(residue_partition(M,h) for M in product(range(q-1),repeat=m))
    for lam in Par(m,h):
        if C[lam]!=count_shape_formula(lam,m,h): bad+=1; print("MISMATCH",q,m,lam,C[lam],count_shape_formula(lam,m,h))
    assert sum(C.values())==(q-1)**m
print("mismatches:",bad)
print("== section 5.10 worked example (q,m)=(9,4) ==")
q,m=9,4; h=4
P3=Par(3,h); print("Par_3:",P3, "Par_4:",Par(4,h), "#downsets Par_4:",len(downsets(Par(4,h))))
for lam in P3: print(lam, count_shape_formula(lam,3,h))
Lam=frozenset([(),(1,1),(2)]); Lam=frozenset([(),(1,1),(2,)])
print("downset?",is_downset(Lam,Par(4,h)))
for mu in P3: print(mu, options(mu,h,q), F_Lambda(mu,Lam,h,q))
Ls=layers(Lam,m,h,q); print("layers:",[sorted(L) for L in Ls])
tot=sum(sum(count_shape_formula(l,3,h) for l in L) for L in Ls); print("|Z_Lambda| via layers:",tot, " brute:",count_Z(Lam,4,h))
Lam2=frozenset([(),(1,1)])
for mu in P3: print("Lam2",mu, F_Lambda(mu,Lam2,h,q))
print("|Z_Lam2|:",count_Z(Lam2,4,h))
print("elapsed %.1fs"%(time.time()-t0))
