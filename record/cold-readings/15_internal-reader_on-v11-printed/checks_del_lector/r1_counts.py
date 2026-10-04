# R1 (Grepy Tinta): counts. Own code. Exact integer arithmetic only.
import itertools, sys
from fractions import Fraction as Fr
from math import factorial, comb
from collections import Counter
def series_mul(a,b,N):
    c=[Fr(0)]*(N+1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b):
            if i+j>N: break
            c[i+j]+=x*y
    return c
def I0(N): return [Fr(1,factorial(i//2)**2) if i%2==0 else Fr(0) for i in range(N+1)]
def cosh(N): return [Fr(1,factorial(i)) if i%2==0 else Fr(0) for i in range(N+1)]
def expx(N): return [Fr(1,factorial(i)) for i in range(N+1)]
def spow(a,e,N):
    r=[Fr(1)]+[Fr(0)]*N
    for _ in range(e): r=series_mul(r,a,N)
    return r
def Nr(r,n):   # n! [x^n] e^x I0^((r-1)/2), r odd >=1
    v=series_mul(expx(n),spow(I0(n),(r-1)//2,n),n)[n]*factorial(n); assert v.denominator==1; return int(v)
def Qodd(k,m):
    N=2*k+2; v=spow(I0(N),(m-1)//2,N)[N]*factorial(N); return int(v)
def Qeven(k,m):
    N=2*k+2; v=series_mul(cosh(N),spow(I0(N),(m-2)//2,N),N)[N]*factorial(N); assert v.denominator==1; return int(v)
def Q(k,m): return Qeven(k,m) if m%2==0 else Qodd(k,m)
def matchings(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for i in range(1,len(S)):
        b=S[i]; rest=S[1:i]+S[i+1:]
        for M in matchings(rest): yield [(a,b)]+M
def gamma_literal(k,m,forbid=None):
    # [DS, Def 1.3]: (a_1..a_{n+1}) in (Z/m \ {0})^{n+1} (additive: a_i != 0), exists J with a_{j_i}+a_{k_i}=0 for the pairs avoiding 0
    n1=2*k+1; Js=[[pr for pr in M if 0 not in pr] for M in matchings(range(n1+1))]
    vals=[a for a in range(1,m) if a!=forbid]
    cnt=0
    for a in itertools.product(vals,repeat=n1):
        for J in Js:
            if all((a[x-1]+a[y-1])%m==0 for x,y in J): cnt+=1; break
    return cnt
print('== P1.1 table of 9.1 ==')
paper={4:[19,141,1107,8953,73789],6:[61,1001,18733,375745,7858225],8:[127,3301,103279,3595177,133789789],
       10:[217,7761,345465,17605249,980612161],12:[331,15101,876331,59415961,4481629021],16:[631,41301,3529863,361612105,42214788925]}
ok=True
for m in paper:
    mine=[Qeven(k,m) for k in range(1,6)]
    print(m,mine,'MATCH' if mine==paper[m] else 'MISMATCH'); ok&=(mine==paper[m])
print('P1.1',ok)
print('Q_1(m)=3m^2-9m+7:',all(Qeven(1,m)==3*m*m-9*m+7 for m in range(4,40,2)))
print('N_{m-1}(N) with e^x equals cosh version:',all(Nr(m-1,2*k+2)==Qeven(k,m) for m in range(4,14,2) for k in range(0,5)))
print('== P1.2 literal Gamma, and DS Rem 4.4 ==')
def ds44(k,m):
    d=1 if m%2==0 else 0
    if k==1: return 3*m*m-9*m+6+d
    if k==2: return 15*m**3-90*m*m+175*m-100+(15*m-39)*d
    if k==3: return 105*m**4-1050*m**3+3955*m*m-6335*m+3325+(210*m*m-1302*m+2010)*d
ok=True
for (k,m) in [(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,12),(3,4)]:
    g=gamma_literal(k,m); q=Q(k,m); d=ds44(k,m)
    print((k,m),'enumerated',g,'formula',q,'DS4.4',d, 'OK' if g==q==d else 'MISMATCH'); ok&=(g==q==d)
print('P1.2',ok)
print('== P1.3 control: forbid -1 ==')
for (k,m) in [(1,4),(1,6),(1,8),(2,4),(2,6)]:
    g=gamma_literal(k,m,forbid=m//2)
    print((k,m),'without -1:',g,'Q_k(m)=',Q(k,m),'Q_k(m-1)=',Qodd(k,m-1),'control fires' if g!=Q(k,m) else 'CONTROL DID NOT FIRE', '(= Q_k(m-1))' if g==Qodd(k,m-1) else '(not Q_k(m-1))')
print('== P1.4/P1.5 Lemma 9.6 ==')
def Nbal(a,q):
    # sum over compositions of a into q parts of (a!/prod c!)^2 = a!^2 [x^a] I0-like: (sum x^c/c!^2)^q
    s=[Fr(1,factorial(c)**2) for c in range(a+1)]
    v=spow(s,q,a)[a]*factorial(a)**2; assert v.denominator==1; return int(v)
def split_count_free(n,q):   # n-tuples in mu_q\{1} that split into inverse pairs (complex mu_q)
    if n%2: return 0
    if q%2==1: v=spow(I0(n),(q-1)//2,n)[n]*factorial(n)
    else: v=series_mul(cosh(n),spow(I0(n),(q-2)//2,n),n)[n]*factorial(n)
    return int(v)
def lemma96(k,m,p,wrong=False,detail=False):
    q=1
    while m%(q*p)==0: q*=p
    rp=m//q; n1=2*k+1
    total=0; ncomp=0; shapes=Counter()
    for c in itertools.product(range(rp),repeat=n1):   # colours as exponents in Z/r'
        c0=(-sum(c))%rp; col=(c0,)+c
        cl=Counter(col)
        okc=True
        if cl[0]%2: okc=False
        if rp%2==0 and cl[rp//2]%2: okc=False
        for z in range(1,rp):
            if 2*z%rp==0: continue
            if cl[z]!=cl[(-z)%rp]: okc=False
        if not okc: continue
        ncomp+=1
        val=split_count_free(cl[0],q)
        if rp%2==0: val*=Nr(q,cl[rp//2])
        for z in range(1,rp):
            if 2*z%rp==0 or z>(-z)%rp: continue
            a=cl[z]
            if wrong and (c0==z or c0==(-z)%rp): val*=Nbal(a-1,q)
            else: val*=Nbal(a,q)
        total+=val
        key=(cl[0],cl[rp//2] if rp%2==0 else 0,tuple(sorted(cl[z] for z in range(1,rp) if 2*z%rp and z<(-z)%rp)))
        shapes[(key,val)]+=1
    if detail: return total,ncomp,shapes
    return total,ncomp
ok=True
for (k,m,p) in [(1,6,2),(1,6,3),(2,6,2),(2,6,3),(1,10,2),(1,10,5),(1,12,2),(1,12,3),(2,12,2),(2,12,3),(1,20,2),(1,20,5)]:
    t,nc=lemma96(k,m,p); tw,_=lemma96(k,m,p,wrong=True)
    print((k,m,p),'sum',t,'Q',Q(k,m),'compatible colourings',nc,'OK' if t==Q(k,m) else 'MISMATCH','| control (0 not a coordinate):',tw,'fires' if tw!=Q(k,m) else 'DID NOT FIRE')
    ok&=(t==Q(k,m))
print('P1.4',ok)
# per-colouring direct enumeration: group the tuples of Gamma (as N-tuples that split) by colour vector
def per_colour_direct(k,m,p):
    q=1
    while m%(q*p)==0: q*=p
    rp=m//q; N=2*k+2
    # mu_m = Z/m additive; colour = a mod r' (via CRT projection Z/m -> Z/r')
    Ms=list(matchings(range(N)))
    cnt=Counter()
    for a in itertools.product(range(1,m),repeat=N-1):
        a0=(-sum(a))%m
        if a0==0: continue
        t=(a0,)+a
        for M in Ms:
            if all((t[x]+t[y])%m==0 for x,y in M):
                cnt[tuple(x%rp for x in a)]+=1; break
    return cnt
for (k,m,p) in [(1,6,2),(1,6,3),(2,6,2),(2,6,3),(1,12,2),(1,12,3)]:
    q=1
    while m%(q*p)==0: q*=p
    rp=m//q
    direct=per_colour_direct(k,m,p)
    bad=0; n1=2*k+1; tot=0
    for c in itertools.product(range(rp),repeat=n1):
        c0=(-sum(c))%rp; cl=Counter((c0,)+c)
        okc=(cl[0]%2==0) and (rp%2 or cl[rp//2]%2==0) and all(cl[z]==cl[(-z)%rp] for z in range(1,rp) if 2*z%rp)
        val=0
        if okc:
            val=split_count_free(cl[0],q)
            if rp%2==0: val*=Nr(q,cl[rp//2])
            for z in range(1,rp):
                if 2*z%rp==0 or z>(-z)%rp: continue
                val*=Nbal(cl[z],q)
        if direct.get(c,0)!=val: bad+=1
        tot+=direct.get(c,0)
    print((k,m,p),'per-colouring: colourings',rp**n1,'mismatches',bad,'total',tot)
print('== P1.6 Example 9.14 ==')
for p in (3,2):
    t,nc,sh=lemma96(1,6,p,detail=True)
    print('p=',p,'total',t,'compatible',nc); 
    for (key,val),mult in sorted(sh.items()): print('   sizes(|C1|,|C-1|,pairs)',key,'value',val,'x',mult)
print('N_3(2),N_3(4),Q_1(3),Q_0(3),Nbal(1,2),Nbal(2,2)=',Nr(3,2),Nr(3,4),Qodd(1,3),Qodd(0,3),Nbal(1,2),Nbal(2,2))
print('== P1.7 Hodge characters ==')
from math import gcd
def hodge(k,m):
    N=2*k+2; units=[t for t in range(1,m) if gcd(t,m)==1]
    B=0; D=0
    # enumerate multisets with multiplicity
    for ms in itertools.combinations_with_replacement(range(1,m),N):
        if sum(ms)%m: continue
        cnt=Counter(ms); mult=factorial(N)
        for v in cnt.values(): mult//=factorial(v)
        isB=all(sum((t*a)%m for a in ms)==(k+1)*m for t in units)
        isD=all(cnt[a]==cnt[m-a] for a in cnt if 2*a!=m) and (m%2 or cnt[m//2]%2==0)
        if isB: B+=mult
        if isD: D+=mult
        if isD and not isB: print('  pair-type not Hodge!?',ms)
    return B,D
for (k,m) in [(1,4),(2,4),(3,4),(4,4),(1,6),(2,6),(1,8),(2,8)]:
    B,D=hodge(k,m); print((k,m),'|B|',B,'|D|',D,'Q',Q(k,m),'|B|-Q',B-Q(k,m),'D==Q',D==Q(k,m))
