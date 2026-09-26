# Gate: |Gamma_{J_s}| = Q_s(m) (m-1)^(d-s), DS Definition 1.3 literal (a_0 = inverse product, a_i != 1 for i>=1)
import itertools
def matchings(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for i in range(1,len(S)):
        for rest in matchings(S[1:i]+S[i+1:]): yield [(a,S[i])]+rest
def gamma(m,d,fams):
    n=2*d; cnt=0
    for a in itertools.product(range(1,m),repeat=n+1):
        A=[(-sum(a))%m]+list(a)
        if any(all((A[j]+A[k])%m==0 for (j,k) in J if 0 not in (j,k)) for J in fams): cnt+=1
    return cnt
for m in (3,5):
  for d in (1,2,3):
    if m==5 and d==3: continue
    full=list(matchings(range(2*d+2)))
    Q={}
    for s in range(0,d+1):
        Q[s]=gamma(m,s,list(matchings(range(2*s+2))))
    for s in range(0,d+1):
        Js=[M+[(2*i,2*i+1) for i in range(s+1,d+1)] for M in matchings(range(2*s+2))]
        g=gamma(m,d,Js); pred=Q[s]*(m-1)**(d-s)
        print(f"m={m} d={d} s={s}: |Gamma_Js|={g} pred Q_s*(m-1)^(d-s)={pred} {'OK' if g==pred else 'FAIL'}")
print("FIN-OK")
