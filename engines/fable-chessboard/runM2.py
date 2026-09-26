# generic Lemma-M check driver.  kind:
#  newclass  PARENTMU n+1 : targets z^2 * G_r(n) (child (1,1) tower r), row 2, trunc z^3, heavy A
#  row0      PARENTMU n+1 : targets G_r(n) in parent|_{z=0}, heavy A
#  raise11   n            : parent (1,1)(n) [+tower rs], child (2,1)(n-1) layer |A'| = s, row q-2 = m, trunc z^(m+1), heavy A' + z
import sys, itertools
from rowM import *
kind=sys.argv[1]; m=int(sys.argv[-1])
def parent(mu,letters,rs):
    if mu==(1,1): return cas11(letters,rs)
    return casilla(mu,letters,False)
def rsof(n,spec):  # tower levels used in the (1,1) casilla at n
    return [int(x) for x in spec.split(',') if x] if spec!='-' else []
if kind in ('newclass','row0'):
    mu=tuple(int(x) for x in sys.argv[2].split(',')); N=int(sys.argv[3]); r=int(sys.argv[4]); prs=rsof(N,sys.argv[5])
    letters=list(range(1,N+1)); z=N; child=list(range(1,N))
    P=parent(mu,letters,prs)
    A=list(range(1,r+1)); rest=[i for i in child if i not in A]
    targets=[]
    for B in itertools.combinations(rest,r):
        body=E([i for i in child if i not in B],len(child)-r-1)
        targets.append(({i:0 for i in A},('x(%d)^2*'%z if kind=='newclass' else '')+'('+body+')'))
    if kind=='newclass':
        print(script(N,P,targets,A,('fixed',z,3),m,'NEWCLASS/VZ row2 %s(%d) <- (1,1)(%d) G_%d'%(mu,N,N-1,r)))
    else:
        print(script(N,P,targets,A,None,m,'ROW0 %s(%d) <- (1,1)(%d) G_%d'%(mu,N,N-1,r),row0z=z))
elif kind=='raise11':
    N=int(sys.argv[2]); s=int(sys.argv[3]); prs=rsof(N,sys.argv[4])
    letters=list(range(1,N+1)); z=N; child=list(range(1,N))
    P=cas11(letters,prs)
    A=list(range(1,s+1)); rest=[i for i in child if i not in A]
    targets=[]
    for B in itertools.combinations(rest,s+1):
        C=[i for i in rest if i not in B]
        targets.append(({**{i:1 for i in A},z:0},'*'.join('x(%d)'%i for i in C) or '1'))
    print(script(N,P,targets,A+[z],(z,1),m,'RAISE (1,1)(%d) row q-2 <- (2,1)(%d) layer |A|=%d'%(N,N-1,s)))
