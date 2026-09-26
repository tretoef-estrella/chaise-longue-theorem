import sys
from rowM import *
from formalq import formal_script
l=int(sys.argv[1]); extra=[int(x) for x in sys.argv[2].split(',') if x] if len(sys.argv)>2 else []
N=7; z=7; letters=list(range(1,8)); child=list(range(1,7))
P=casilla((2,1),letters,False)
T=[(h,b) for h,b in family(2,2,child)]
j=1
# target phi_{1,l}(6) = y_1^(q-2) e_2(y' minus l): family() order: for j, for l
tg=[({**h,z:0},b) for (h,b),(jj,ll) in zip(T,[(a,c) for a in child for c in child if a!=c]) if jj==j and ll==l]
print(formal_script(N,P,tg,[j,l,z]+extra,(z,1),'(ii) (2,1)(7) raise <- (2,2)(6) phi_{1,%d}'%l,K=int(sys.argv[3]) if len(sys.argv)>3 else 2))
