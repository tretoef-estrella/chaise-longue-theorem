# formal-q driver (Fable 12).  modes as runM2:  row0layer N r rs Hextra K  |  newclass MU N r rs Hextra K  |  row0 MU N r rs Hextra K
import sys, itertools
from rowM import *
from formalq import formal_script
mode=sys.argv[1]
def parse(s): return [int(x) for x in s.split(',') if x] if s not in ('-','') else []
if mode=='row0layer':    # row 0 of (1,1)(N) [K^unif + tower rs] contains (1)(N-1) layer |A| = r, targets restricted to B given
    N=int(sys.argv[2]); r=int(sys.argv[3]); rs=parse(sys.argv[4]); Hx=sys.argv[5]; K=int(sys.argv[6]); Bsel=parse(sys.argv[7]) if len(sys.argv)>7 else None
    letters=list(range(1,N+1)); z=N; child=list(range(1,N)); P=cas11(letters,rs)
    A=list(range(1,r+1)); rest=[i for i in child if i not in A]; out=[]
    for B in itertools.combinations(rest,r):
        if Bsel and list(B)!=Bsel: continue
        C=[i for i in rest if i not in B]
        tg=[({i:1 for i in A},'*'.join('x(%d)'%i for i in C) or '1')]
        H=A+(list(B) if Hx=='B' else parse(Hx))
        print(formal_script(N,P,tg,H,None,'ROW0 (1,1)(%d) <- (1)(%d) |A|=%d B=%s'%(N,N-1,r,list(B)),row0z=z,K=K)); break
elif mode in ('newclass','row0'):
    mu=tuple(parse(sys.argv[2])); N=int(sys.argv[3]); r=int(sys.argv[4]); rs=parse(sys.argv[5]); Hx=sys.argv[6]; K=int(sys.argv[7])
    letters=list(range(1,N+1)); z=N; child=list(range(1,N))
    P=cas11(letters,rs) if mu==(1,1) else casilla(mu,letters,False)
    A=list(range(1,r+1)); rest=[i for i in child if i not in A]
    B=rest[:r]    # one representative target (by symmetry)
    body=E([i for i in child if i not in B],len(child)-r-1)
    tg=[({i:0 for i in A},('x(%d)^2*'%z if mode=='newclass' else '')+'('+body+')')]
    H=A+(list(B) if Hx=='B' else parse(Hx))
    if mode=='newclass': print(formal_script(N,P,tg,H,('fixed',z,3),'NEWCLASS %s(%d) <- G_%d(%d) B=%s'%(mu,N,r,N-1,B),K=K))
    else: print(formal_script(N,P,tg,H,None,'ROW0 %s(%d) <- G_%d(%d) B=%s'%(mu,N,r,N-1,B),row0z=z,K=K))
