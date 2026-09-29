import itertools
from math import factorial
def matchings(S):
    S=list(S)
    if not S: yield {}; return
    a=S[0]
    for b in S[1:]:
        rest=[x for x in S if x not in (a,b)]
        for M in matchings(rest):
            M=dict(M); M[a]=b; M[b]=a; yield M
def pm(n): return 0 if n%2 else (factorial(n)//(2**(n//2)*factorial(n//2)) if n else 1)
checks=0;fails=0
for r in (3,5,7):
    R=[z for z in range(1,r) if z< r-z]   # representatives: z < -z mod r
    for N in (2,4,6):
        V=list(range(N))
        for col in itertools.product(range(r),repeat=N):   # additive: c_a c_b =1  <=> col[a]+col[b]=0
            C={z:[v for v in V if col[v]==z] for z in range(r)}
            # (i)
            for a in V:
                for b in V:
                    if a==b: continue
                    lhs=(col[a]+col[b])%r==0
                    rhs=(col[a]==0 and col[b]==0) or any((col[a]==z and col[b]==r-z) or (col[a]==r-z and col[b]==z) for z in R)
                    checks+=1; fails+= lhs!=rhs
            comp=[M for M in matchings(V) if all((col[a]+col[M[a]])%r==0 for a in V)]
            # (ii) count = pm(|C0|) * prod |C_z|! if |C_z|=|C_-z|
            ok_sizes=len(C[0])%2==0 and all(len(C[z])==len(C[r-z]) for z in R)
            expected= pm(len(C[0]))*eval('*'.join([str(factorial(len(C[z]))) for z in R]) or '1') if ok_sizes else 0
            checks+=1; fails+= len(comp)!=expected
            # (ii') characterisation: each compatible M maps C0->C0, Cz->C-z ; restriction map injective
            sig=set()
            for M in comp:
                good=all(col[M[a]]==(-col[a])%r for a in V); checks+=1; fails+= not good
                sig.add(tuple(sorted(M.items())))
            # (iii)
            checks+=1; fails+= (len(comp)>0)!=ok_sizes
            # (iv) if sum col ==0: compatibility <=> pairs not containing 0 compatible
            if sum(col)%r==0:
                for M in matchings(V):
                    a1=all((col[a]+col[M[a]])%r==0 for a in V)
                    a2=all((col[a]+col[M[a]])%r==0 for a in V if a!=0 and M[a]!=0)
                    checks+=1; fails+= a1!=a2
        print(r,N,checks,fails)
print('TOTAL',checks,fails)
