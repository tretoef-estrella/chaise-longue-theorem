import sys, itertools
PR=int(sys.argv[1])
src=open('chk8.py').read().split('fails=checks=0')[0].replace('P=101',f'P={PR}',1)
exec(src)
def resPart(M,h):
    parts=[]
    for u in range(1,h+1):
        a=M.count(u); b=M.count(-u)
        if a!=b: parts.append(abs(a-b))
    return tuple(sorted(parts,reverse=True))
bad=tot=strict=0
for q,mmax in ((3,5),(5,4),(7,3),(9,2)):
    h=(q-1)//2; T=[s*u for u in range(1,h+1) for s in (1,-1)]
    for m in range(0,mmax+1):
        Par=parts_list(m,h)
        for Lam in downsets(Par):
            if not Lam: continue
            if m==0: dimV=1 if () in Lam else 0
            else:
                V,M,idx=VLam(Lam,range(m),m,q); dimV=len(V)
            Z=sum(1 for M in itertools.product(T,repeat=m) if resPart(list(M),h) in Lam)
            tot+=1
            if dimV!=Z: strict+=1; print('DIFF',q,m,Lam,dimV,Z)
print('P',PR,'checks',tot,'dim != |Z|:',strict)
