# T1: row 0 of (1,1)(n) [K^unif + F2 if n in F2cells] contains the child (1)(n-1) layer N_0 with |A| = r (targets heavy in A).
import sys, itertools
from rowM import *
n=int(sys.argv[1]); r=int(sys.argv[2]); m=int(sys.argv[3]); withF2=sys.argv[4]=='F2'
z=n; letters=list(range(1,n+1)); child=list(range(1,n))
P=casilla((1,1),letters,withF2)
A=list(range(1,r+1)); rest=[i for i in child if i not in A]
targets=[]
for B in itertools.combinations(rest,r):
    C=[i for i in rest if i not in B]
    targets.append(({i:1 for i in A},'*'.join('x(%d)'%i for i in C) or '1'))
print(script(n,P,targets,A,None,m,'ROW0 (1,1) n=%d %s |A|=%d'%(n,'K+F2' if withF2 else 'Kunif',r),row0z=z))
