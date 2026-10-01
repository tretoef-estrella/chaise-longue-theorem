# Graded S_n-character prediction: tr(sigma|A_d) = sum_lam [t^d] t^{mn} m0_lam(1/t) * tr(sigma | M_lam),
# M_lam = Hom_{so(2m+1)}(V_lam, V^{(x)n}); tr(sigma|M_lam) from Adams operations + Brauer-Klimyk.
import itertools,re
exec(open('lusztig_B.py').read().split('data={}')[0])
def weights_V(m):
    W=[tuple([0]*m)]
    for i in range(m):
        for s in (1,-1):
            v=[0]*m; v[i]=s; W.append(tuple(v))
    return W
def mult_from_char(m,char,Wg):
    rho2=tuple(2*m-1-2*i for i in range(m))
    out={}
    for mu,c in char.items():
        v2=tuple(2*a+b for a,b in zip(mu,rho2))
        # find w making v2 dominant strictly
        a=[abs(x) for x in v2]; 
        # sign of w: reflections: sign flips count + permutation sorting parity
        flips=sum(1 for x in v2 if x<0)
        order=sorted(range(m),key=lambda i:-a[i]); srt=[a[i] for i in order]
        if any(srt[i]==srt[i+1] for i in range(m-1)) or srt[-1]==0: continue
        par=0
        for i in range(m):
            for j in range(i+1,m):
                if order[i]>order[j]: par+=1
        sg=(-1)**(flips+par)
        lam=tuple((srt[i]-rho2[i])//2 for i in range(m))
        out[lam]=out.get(lam,0)+sg*c
    return {k:v for k,v in out.items() if v}
tr_data={}
for line in open('../regla_puente_teoremaA_2026-10-01/traces.log'):
    mm=re.match(r'q=(\d+) n=(\d+) lam=\{(.*)\} tr=\{(.*)\}',line)
    if mm:
        tr_data[(int(mm[1]),int(mm[2]),tuple(int(x) for x in mm[3].split(',')))]=[int(x) for x in mm[4].split(',')]
ok=0;tot=0
cache={}
for (q,n,rho),tr in sorted(tr_data.items()):
    m=(q-1)//2
    if m not in cache: cache[m]=make(m)
    m0=cache[m]; WV=weights_V(m)
    char={tuple([0]*m):1}
    for k in rho:
        new={}
        for mu,c in char.items():
            for w in WV:
                nu=tuple(a+k*b for a,b in zip(mu,w)); new[nu]=new.get(nu,0)+c
        char=new
    M=mult_from_char(m,char,None)
    pred={}
    for lam,c in M.items():
        for d,v in m0(lam).items():
            D=m*n-d; pred[D]=pred.get(D,0)+c*v
    L=max([k for k,v in pred.items() if v]+[0])+1
    p=[pred.get(d,0) for d in range(L)]
    while p and p[-1]==0: p.pop()
    tot+=1; good=(p==tr); ok+=good
    if not good: print('NO',q,n,rho,p,tr)
print('graded traces matching',ok,'of',tot)
