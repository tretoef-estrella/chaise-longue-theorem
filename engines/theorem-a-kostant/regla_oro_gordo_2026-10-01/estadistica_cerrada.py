# Closed statistic: deg(w) = m*n - cod(w),
# cod(w) = sum over loop steps of z(p)  +  sum over steps returning coord i to 0 of label,
# label = 2*#{k<i : p_k = 0 after the step} + (0 if came from +1 else 1)
import itertools,sys
def walks(m,n):
    S=[None]+[(i,s) for i in range(m) for s in (1,-1)]
    for w in itertools.product(S,repeat=n):
        p=[0]*m
        for st in w:
            if st: p[st[0]]+=st[1]
        if all(x==0 for x in p): yield w
def cod(m,w,side_minus_zero=True):
    p=[0]*m; c=0
    for st in w:
        if st is None:
            c+=sum(1 for x in p if x==0)
        else:
            i,s=st; prev=p[i]; p[i]+=s
            if p[i]==0:
                lab=2*sum(1 for k in range(i) if p[k]==0)+(0 if prev==1 else 1)
                c+=lab
    return c
data={}
for line in open('../regla_puente_teoremaA_2026-10-01/hfall.log'):
    pp=line.split(); q=int(pp[0][2:]); n=int(pp[1][2:])
    data[(q,n)]=[int(x) for x in line.split('{')[1].split('}')[0].split(',')]
ok=0;tot=0
for (q,n),hf in sorted(data.items()):
    m=(q-1)//2
    if (2*m+1)**n>3e6: continue
    H=[0]*(m*n+1)
    for w in walks(m,n): H[m*n-cod(m,w)]+=1
    while H and H[-1]==0: H.pop()
    tot+=1; ok+= H==hf
    print(q,n,H==hf,H if H!=hf else '')
print('closed statistic matches',ok,'of',tot)
