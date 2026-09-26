# INFORME_8 STEP 2: generate M2 script computing all rows of K_(m,1)(n+1) at q, with the dictionary of STEP 0.5 and fibre sizes from fibre.py
import sys
from fibre import W
q=int(sys.argv[1]); cells=eval(sys.argv[2]); out=sys.argv[3]
def dictionary(mu,n,q):
    # rows a=0..q-1 -> profile mu+v in n-1 variables; lowering (larger fibre first), 0, new class, raising (larger fibre first)
    mu=list(mu); l=len(mu)
    low=[]; 
    for i in range(l):
        nu=mu[:]; nu[i]-=1; nu=tuple(sorted([x for x in nu if x>0],reverse=True)); low.append(nu)
    low=sorted(set(low), key=lambda nu:-W(nu,n-1,q))
    # keep multiplicity: distinct parts give distinct profiles; equal parts give the same profile twice
    lows=[]
    for i in range(l):
        nu=mu[:]; nu[i]-=1; nu=tuple(sorted([x for x in nu if x>0],reverse=True)); lows.append(nu)
    lows=sorted(lows, key=lambda nu:-W(nu,n-1,q))
    raises=[]
    for i in range(l):
        nu=mu[:]; nu[i]+=1; nu=tuple(sorted(nu,reverse=True)); raises.append(nu)
    raises=sorted(raises, key=lambda nu:-W(nu,n-1,q))
    new=tuple(sorted(mu+[1],reverse=True))
    return lows+[tuple(mu)]+[new]*(q-1-2*l)+raises
lines=[]
lines.append('q = %d;'%q)
lines.append(open('rows2_body.m2').read())
for (nn,m) in cells:
    mu=(m,1); n=nn-1
    dic=dictionary(mu,nn,q)
    prof='{'+','.join('{'+','.join(map(str,nu))+'}' for nu in dic)+'}'
    fib='{'+','.join(str(W(nu,n,q)) for nu in dic)+'}'
    lines.append('doCell(%d, %d, %s, %s);'%(nn,m,prof,fib))
lines.append('<< "FIN-OK" << endl;')
open(out,'w').write('\n'.join(lines)+'\n')
print("wrote",out)
for (nn,m) in cells:
    print((nn,m), dictionary((m,1),nn,q), [W(nu,nn-1,q) for nu in dictionary((m,1),nn,q)], "sum", sum(W(nu,nn-1,q) for nu in dictionary((m,1),nn,q)), "fibre", W((m,1),nn,q))
