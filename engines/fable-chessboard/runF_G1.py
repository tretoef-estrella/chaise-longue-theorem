import sys
from rowM import *
from formalq import formal_script
N=int(sys.argv[1]); extra=[int(x) for x in sys.argv[2].split(',') if x] if len(sys.argv)>2 else []
z=N; letters=list(range(1,N+1)); child=list(range(1,N))
P=casilla((1,),letters,False)
j,l=1,2
tg=[({j:0},'x(%d)^2*%s'%(z,E([i for i in child if i!=l],len(child)-2)))]
print(formal_script(N,P,tg,[j,l]+extra,("fixed",z,3),'(G1) (1)(%d) row2 <- (1,1)(%d) phi_12'%(N,N-1),K=int(sys.argv[3]) if len(sys.argv)>3 else 0))
