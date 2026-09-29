exec(open('chk18.py').read().split('cells=[')[0])
import itertools, sys
def dimV(q,a,b,p,L):
    n=a+b; mons=list(itertools.product(range(q),repeat=n)); col={e:k for k,e in enumerate(mons)}
    rows=[]
    for lam in L:
        for t in tight_patterns(lam,a,b):
            G=product(t,a,b,q,p)
            for m in mons:
                h=pmul({m:1},G,q,p)
                if h:
                    v=[0]*len(mons)
                    for e,c in h.items(): v[col[e]]=c
                    rows.append(v)
    piv,R=rref(rows,len(mons),p); return len(piv)
def ZL(q,a,b,L):
    return sum(1 for xi in itertools.product(range(q),repeat=a) for eta in itertools.product(range(q),repeat=b) if shape(xi,eta) in L)
tot=0;bad=0;eq=0
for q,a,b,p in [(3,0,0,3),(3,1,0,3),(3,0,2,3),(3,1,1,3),(3,2,1,3),(3,1,2,3),(3,2,2,3),(3,3,1,3),(3,0,3,3),(3,3,0,3),(5,1,1,5),(5,2,1,5),(5,1,2,5),(7,1,1,7),(3,2,2,101),(5,1,1,101),(3,1,1,2)]:
    for L in downsets(BPar(q,a,b)):
        d=dimV(q,a,b,p,L); z=ZL(q,a,b,L); tot+=1
        if d<z: bad+=1
        if d==z: eq+=1
    print(q,a,b,p,'cum',tot,bad,eq); sys.stdout.flush()
print('Theorem 7.6: down-sets',tot,'failures',bad,'equalities',eq)
# Theorem C roots
for q,p in [(3,3),(5,5),(3,101)]:
    for a in range(0,3):
        Lb={((),())}; Lp={((1,),())}
        print('q=%d p=%d a=%d: dim Ibal %d >= Nbal %d ; dim Iph %d >= Nph %d'%(q,p,a,dimV(q,a,a,p,Lb),ZL(q,a,a,Lb),dimV(q,a+1,a,p,Lp),ZL(q,a+1,a,Lp)))
