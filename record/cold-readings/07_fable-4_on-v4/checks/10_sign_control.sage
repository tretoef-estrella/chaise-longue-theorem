# Section 8.4's remark: with 1+t in place of 1-t in psi_J, the rank at (n,m)=(2,3) would not be 7.  Test over Q with the literal ring R=Z[t1,t2,t3]/(t_i^3-1):
# rank L(X) = rank(ideal)+1.  Prediction: correct psi gives 7; the sign-flipped one gives something else.  Also the same at (1,5): 37.
import sys, itertools; sys.path.insert(0,'checks')
from lib_chaise import matchings, Qk
for (k,q) in [(1,3),(1,5),(2,3)]:
    m=2*k+1; N=2*k+2
    R=PolynomialRing(QQ,m,'t'); t=R.gens(); phi=lambda u: sum(u^i for i in range(q))
    box=[v^q-1 for v in t]
    for sign,name in [(-1,"1-t (DS)"),(1,"1+t (flipped)")]:
        gens=[]
        for J in matchings(range(N)):
            g=R(1)
            for a,b in J:
                a,b=min(a,b),max(a,b)
                g*=(t[b-1]+sign)
                if a>0: g*=phi(t[a-1]*t[b-1])
            gens.append(g)
        I=R.ideal(gens+box); d=I.vector_space_dimension()
        print("(k,q)=(%d,%d) %s: rank(ideal)=%d, rank L(X) = %d (Q_k(q)+1 = %d)"%(k,q,name,q^m-d,q^m-d+1,Qk(k,q)+1), flush=True)
