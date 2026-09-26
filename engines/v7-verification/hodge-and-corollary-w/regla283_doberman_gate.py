# Gate: Rafa's repo DOBERMAN/verdict tables (README (47)) vs our Lemma 2.2: |Gamma| = DIM - dim_C = Q_k(m) for odd m,
# with Q_k(m) = (2k+2)! [x^{2k+2}] I_0(2x)^{(m-1)/2}, I_0(2x) = sum x^{2b}/(b!)^2.
import re, sys
from fractions import Fraction
from math import factorial
t=open(sys.argv[1],encoding='utf-8').read()
rows=re.findall(r'^\| \((\d+),(\d+)\) \| ([\d,]+) \| (?:\d[\d,]* \| )?([\d,]+) \|',t,re.M)
def Q(k,m):
    N=2*k+2; h=(m-1)//2
    ser=[Fraction(0)]*(N+1)
    for b in range(0,N//2+1): ser[2*b]=Fraction(1,factorial(b)**2)
    p=[Fraction(0)]*(N+1); p[0]=Fraction(1)
    for _ in range(h):
        q=[Fraction(0)]*(N+1)
        for i,a in enumerate(p):
            if a:
                for j in range(0,N+1-i):
                    if ser[j]: q[i+j]+=a*ser[j]
        p=q
    return int(p[N]*factorial(N))
seen=set(); ok=bad=0
for n,m,DIM,dimC in rows:
    n,m=int(n),int(m); DIM=int(DIM.replace(',','')); dimC=int(dimC.replace(',',''))
    if (n,m) in seen or m%2==0: continue
    seen.add((n,m)); k=n//2
    assert DIM==(m-1)**(n+1),(n,m)
    g=DIM-dimC; q=Q(k,m); st='OK' if g==q else 'FAIL'
    ok+= g==q; bad+= g!=q
    print(f"(n,m)=({n},{m}) k={k}: DIM-dim_C={g}  Q_k(m)={q}  {st}")
print("OK",ok,"FAIL",bad); print("FIN-OK")
