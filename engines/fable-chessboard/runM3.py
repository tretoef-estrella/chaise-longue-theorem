# unrestricted / partially restricted variant: heavy set = A + extra letters (given), or 'all'
import sys, itertools
from rowM import *
kind=sys.argv[1]; mu=tuple(int(x) for x in sys.argv[2].split(',')); N=int(sys.argv[3]); r=int(sys.argv[4]); prs=[int(x) for x in sys.argv[5].split(',') if x] if sys.argv[5]!='-' else []
Hs=sys.argv[6]; m=int(sys.argv[7])
letters=list(range(1,N+1)); z=N; child=list(range(1,N))
P=cas11(letters,prs) if mu==(1,1) else casilla(mu,letters,False)
A=list(range(1,r+1)); rest=[i for i in child if i not in A]
targets=[]
for B in itertools.combinations(rest,r):
    body=E([i for i in child if i not in B],len(child)-r-1)
    targets.append(({i:0 for i in A},('x(%d)^2*'%z if kind=='newclass' else '')+'('+body+')'))
H=letters if Hs=='all' else A+[int(x) for x in Hs.split(',') if x]
if kind=='newclass': print(script(N,P,targets,H,('fixed',z,3),m,'NEWCLASS %s(%d) <- G_%d H=%s'%(mu,N,r,Hs)))
else: print(script(N,P,targets,H,None,m,'ROW0 %s(%d) <- G_%d H=%s'%(mu,N,r,Hs),row0z=z))
