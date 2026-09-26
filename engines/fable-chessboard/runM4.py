# (ii): parent (2,1)(7) raise row q-2 = m  ⊇  child (2,2)(6) generators, each target z^m * g, trunc z^(m+1), heavy = heavy(g) + z
import sys, itertools
from rowM import *
m=int(sys.argv[1]); part=sys.argv[2]
N=7; z=7; letters=list(range(1,8)); child=list(range(1,7))
P=casilla((2,1),letters,False)
C=casilla((2,2),child,False)   # Q + box + family + layer N_1
if part=='Q': T=Qgens((2,2),child)
elif part=='box': T=box(child)
elif part=='fam': T=family(2,2,child)
elif part=='layer': T=layer(1,child)
out=[]; bad=0
# group targets by heavy set
groups={}
for h,b in T: groups.setdefault(tuple(sorted(h)),[]).append((h,b))
for H,tg in groups.items():
    targets=[({**h,z:0},b) for h,b in tg]   # z^m (offset 0) times target
    print(script(N,P,targets,list(H)+[z],(z,1),m,'(ii) (2,1)(7) raise <- (2,2)(6) %s heavy %s'%(part,list(H))))
