import sys, itertools
from rowM import *
n=int(sys.argv[1]); r=int(sys.argv[2]); m=int(sys.argv[3]); withF2=sys.argv[4]=='F2'; Hmode=sys.argv[5]
z=n; letters=list(range(1,n+1)); child=list(range(1,n))
P=casilla((1,1),letters,withF2)
A=list(range(1,r+1)); rest=[i for i in child if i not in A]
targets=[]
for B in itertools.combinations(rest,r):
    C=[i for i in rest if i not in B]
    targets.append(({i:1 for i in A},'*'.join('x(%d)'%i for i in C) or '1'))
H=A if Hmode=='A' else (child if Hmode=='all' else A+[int(x) for x in Hmode.split(',')])
print(script(n,P,targets,H,None,m,'ROW0 (1,1) n=%d %s |A|=%d'%(n,'K+F2' if withF2 else 'Kunif',r),row0z=z))
