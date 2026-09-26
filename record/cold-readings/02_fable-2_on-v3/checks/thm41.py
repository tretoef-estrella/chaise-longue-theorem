"""Theorem 4.1 (q=3), my own implementation of (i)-(ii):
 for every U in the set of ballot-type subsets, build (J,T) by the greedy rule of (ii), expand y_T D_J in C=F_3[y]/(y_i^2),
 check LM = +-y_U (lex y_1>...>y_n'); and check by brute force (k<=4) that no y_T D_J has a leading monomial outside {y_U}."""
import itertools, sys
from boxalg import matchings
def expand(T, J, n):
    # y_T * prod_{(a,b) in J, a!=0} (y_b - y_a), squarefree ring: dict frozenset->coeff mod 3
    poly={frozenset(T):1}
    for (a,b) in J:
        if a==0: continue
        a-=1; b-=1
        new={}
        for mon,c in poly.items():
            for var,s in ((b,1),(a,-1)):
                if var in mon: continue
                m2=mon|{var}; new[m2]=(new.get(m2,0)+c*s)%3
        poly={m:c for m,c in new.items() if c}
    return poly
def LM(poly,n):
    # lex with y_1 > y_2 > ... : compare exponent vectors
    best=None
    for mon,c in poly.items():
        vec=tuple(1 if i in mon else 0 for i in range(n))
        if best is None or vec>best[0]: best=(vec,c)
    return best
def ballot(n):
    out=[]
    for bits in itertools.product([0,1],repeat=n):
        h=0; ok=True
        for b in bits:
            h+= 1 if b else -1
            if h<-1: ok=False;break
        if ok: out.append(frozenset(i for i in range(n) if bits[i]))
    return out
def construct(U,n):
    up=[]; matched=[]; unmatched_down=[]
    for i in range(n):
        if i in U: up.append(i)
        else:
            if up: a=up.pop(); matched.append((a,i))
            else: unmatched_down.append(i)
    assert len(unmatched_down)<=1
    if unmatched_down: c=unmatched_down[0]; rem=up
    else: c=up[-1]; rem=up[:-1]
    assert len(rem)%2==0
    full=[(rem[i],rem[i+1]) for i in range(0,len(rem),2)]
    J=tuple(sorted([(0,c+1)]+[(a+1,b+1) for a,b in matched+full]))
    T=set(a for a,b in full)
    if c in U: T.add(c)
    return J,T
for k in range(1,7):
    n=2*k+1; B=ballot(n); bad=0
    for U in B:
        J,T=construct(U,n)
        lm=LM(expand(T,J,n),n)
        if lm is None or frozenset(i for i in range(n) if lm[0][i])!=U or lm[1] not in (1,2): bad+=1; print("FAIL",k,sorted(U),J,T,lm)
    from math import comb
    print(f"k={k}: |U|={len(B)} = C(2k+2,k+1)={comb(2*k+2,k+1)}  construction failures={bad}", flush=True)
    if k<=4:
        seen=set(); outside=0
        for J in matchings(2*k+2):
            for r in range(n+1):
                for T in itertools.combinations(range(n),r):
                    lm=LM(expand(T,J,n),n)
                    if lm is None: continue
                    U=frozenset(i for i in range(n) if lm[0][i]); seen.add(U)
                    if U not in set(B): outside+=1
        print(f"   brute force k={k}: leading monomials of all y_T D_J: {len(seen)} distinct, {outside} outside the ballot set; ballot set fully reached: {set(B)<=seen}", flush=True)
