import re, itertools
data={}
for line in open('traces.log'):
    m=re.match(r'q=(\d+) n=(\d+) lam=\{(.*)\} tr=\{(.*)\}',line)
    if m: data.setdefault((int(m[1]),int(m[2])),{})[tuple(int(x) for x in m[3].split(','))]=[int(x) for x in m[4].split(',')]
def perm(lam,n):
    p=list(range(n)); st=0
    for c in lam:
        for j in range(c): p[st+j]=st+(j+1)%c
        st+=c
    return p
tot=0; ok=0
for (q,n),D in sorted(data.items()):
    # Z = points of F_q^n (q prime here) whose multiset is closed under negation
    Z=[x for x in itertools.product(range(q),repeat=n) if all(x.count(v)==x.count((-v)%q) for v in range(q)) and x.count(0)%2==n%2*0+ (x.count(0)%2)]
    Z=[x for x in itertools.product(range(q),repeat=n) if all(x.count(v)==x.count((-v)%q) for v in range(1,q))]
    for lam,tr in D.items():
        s=perm(lam,n)
        act=lambda x: tuple(x[s.index(i)] for i in range(n))   # (sigma.x)_i = x_{sigma^{-1}(i)}
        fix=sum(1 for x in Z if act(x)==x)
        neg=sum(1 for x in Z if act(x)==tuple((-v)%q for v in x))
        a=sum(tr); b=sum((-1)**d*v for d,v in enumerate(tr))
        tot+=1; good=(a==fix and b==neg); ok+=good
        if not good or lam==tuple([1]*n): print(f'q={q} n={n} lam={lam}: sum tr={a} fix={fix} | alt sum tr={b} sigma(x)=-x: {neg}  {"OK" if good else "FALLA"}')
print(f'TOTAL {ok}/{tot} clases de conjugación cumplen las dos igualdades')
