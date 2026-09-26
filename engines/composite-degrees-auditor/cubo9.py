# Item 8: |B(k,9)| = C(2k+2,k+1)^3. Direct count of Hodge characters vs the sign-vector bijection.
import itertools, collections
from math import comb
m=9; units=[t for t in range(1,m) if t%3]
def hodge_count(k):
    N=2*k+2; cnt=0
    # count via multisets: generating function over residues 1..8
    # dynamic programming over (sum of <a>, <2a>, <4a> ) deviations
    dp=collections.Counter({(0,0,0):1})
    for _ in range(N):
        nd=collections.Counter()
        for (s1,s2,s4),c in dp.items():
            for a in range(1,m):
                nd[(s1+2*((a)%m)-m, s2+2*((2*a)%m)-m, s4+2*((4*a)%m)-m)]+=c
        dp=nd
    return dp[(0,0,0)]
def hodge_brute(k):
    N=2*k+2; c=0
    for al in itertools.product(range(1,m),repeat=N):
        if sum(al)%m: continue
        if all(sum((t*a)%m for a in al)==m*(k+1) for t in units): c+=1
    return c
print("k=1 brute:",hodge_brute(1),"dp:",hodge_count(1),"C^3:",comb(4,2)**3)
for k in (2,3,4):
    print(f"k={k} dp:",hodge_count(k),"C^3:",comb(2*k+2,k+1)**3)
# the linear map: deviations (2<ta>-9)_{t=1,2,4} vs sign vectors
dev={a:tuple(2*((t*a)%m)-m for t in (1,2,4)) for a in range(1,m)}
sgn={a:tuple(1 if x>0 else -1 for x in v) for a,v in dev.items()}
print("sign map bijective:",len(set(sgn.values()))==8)
import numpy as np
A=np.array([sgn[a] for a in (1,2,4)],float).T; B=np.array([dev[a] for a in (1,2,4)],float).T
M=B@np.linalg.inv(A)
print("M=",M.round(6).tolist(),"det",round(np.linalg.det(M),6))
print("dev = M·sgn for all 8 residues:",all(np.allclose(M@np.array(sgn[a]),dev[a]) for a in range(1,m)))
