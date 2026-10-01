import re
R.<t> = QQ[]
Sym = SymmetricFunctions(FractionField(R)); s=Sym.schur(); p=Sym.power(); h=Sym.homogeneous(); e=Sym.elementary()
data={}
for line in open('../regla_puente_teoremaA_2026-10-01/traces.log'):
    m=re.match(r'q=(\d+) n=(\d+) lam=\{(.*)\} tr=\{(.*)\}',line)
    if m:
        q,n=int(m[1]),int(m[2]); lam=Partition([int(x) for x in m[3].split(',')]); tr=[int(x) for x in m[4].split(',')]
        data.setdefault((q,n),{})[lam]=tr
def frob(q,n):
    F=0
    for lam,tr in data[(q,n)].items():
        F+= sum(QQ(tr[d])*t^d for d in range(len(tr)))*p(lam)/lam.centralizer_size()
    return s(F)
for (q,n) in sorted(data):
    if q!=3: continue
    F=frob(q,n)
    D={}
    for la,c in F:
        for d,v in enumerate(R(c).list()):
            if v: D.setdefault(d,[]).append((v,list(la)))
    print('q',q,'n',n)
    for d in sorted(D): print('   d',d,D[d])
