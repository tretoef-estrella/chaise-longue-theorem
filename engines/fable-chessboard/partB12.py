# PART B check (Fable 12): at f = 2, child (2,1^{L-2}) at n = L+2 (L = |mu|, ell = L-1 parts):
#  (I11) a^{q-1} x_C  ==  sum_{i=1,2} h_{L-2}(a, -b_{3-i}) * phi_{a b_i}   mod  J0 := (e_1, e_3, e_4, ..., e_n) + (x_{[n]\b} : b) + box
#  phi = child's family  phi^{(ell)}_{jl} = y_j^{q-ell} sum_{i<ell} y_j^i e_{f+ell-2-i}(y\{j,l})
#  and (full) N_1 layer inside Q + box + F.
import sys, itertools
L=int(sys.argv[1]); q=int(sys.argv[2]); ell=L-1; n=L+2; f=2
mu=[2]+[1]*(ell-1)
out=['ring r = %d, (x(1..%d)), dp;'%(3 if q==3 else 3, n)] if False else []
out=['ring r = (%d,w), (x(1..%d)), dp;'%(q,n) if q>3 else 'ring r = 3, (x(1..%d)), dp;'%n]
out.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }')
X=lambda S: 'list(%s)'%(', '.join('x(%d)'%i for i in S))
allv=list(range(1,n+1))
J0=['elv(%s,%d)'%(X(allv),j) for j in range(1,n+1) if j%2==1 or j>=f+1]
J0+=['x(%d)^%d'%(i,q) for i in allv]
J0+=['*'.join('x(%d)'%i for i in allv if i!=b) for b in allv]
# Tanisaki proper subsets of Q (lambda = mu u 1^f)
lam=mu+[1]*f; conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
def dk(k): return sum(conj[n-k:]) if k>0 else 0
Tan=[]
for k in range(1,n):
    for Ss in itertools.combinations(allv,k):
        for rr in range(max(1,k-dk(k)+1),k+1): Tan.append('elv(%s,%d)'%(X(Ss),rr))
def phi(j,l):
    P=[i for i in allv if i not in (j,l)]
    return '(' + '+'.join('x(%d)^%d*elv(%s,%d)'%(j,q-ell+i,X(P),f+ell-2-i) for i in range(ell)) + ')'
Fam=[phi(j,l) for j in allv for l in allv if j!=l]
out.append('ideal J0 = %s; ideal SJ0 = std(J0);'%(', '.join(J0)))
out.append('ideal J = J0, %s, %s; ideal SJ = std(J);'%(', '.join(Tan) if Tan else '0', ', '.join(Fam)))
a,b1,b2=1,2,3; C=[i for i in allv if i not in (a,b1,b2)]
def h(D,u,v):   # h_D(u,v) with u,v strings
    if D<0: return '0'
    return '(' + '+'.join('(%s)^%d*(%s)^%d'%(u,i,v,D-i) for i in range(D+1)) + ')'
lhs='x(%d)^%d*%s'%(a,q-1,'*'.join('x(%d)'%i for i in C))
rhs='%s*%s + %s*%s'%(h(L-2,'x(%d)'%a,'-x(%d)'%b2),phi(a,b1),h(L-2,'x(%d)'%a,'-x(%d)'%b1),phi(a,b2))
out.append('poly dI = %s - (%s); "L=%d q=%d n=%d: (I11) identity mod J0:", reduce(dI, SJ0) == 0, "  mod J0+Tan+F:", reduce(dI, SJ) == 0;'%(lhs,rhs,L,q,n))
# full layer N_1 in Q + box + F
cnt=0; lines=[]
for na in range(0,n):
    nb=na+1
    for A in itertools.combinations(allv,na):
        rest=[i for i in allv if i not in A]
        for B in itertools.combinations(rest,nb):
            Cc=[i for i in rest if i not in B]
            mono='*'.join(['x(%d)^%d'%(i,q-1) for i in A]+['x(%d)'%i for i in Cc]) or '1'
            lines.append('tot++; if (reduce(%s, SJ) != 0) { bad++; }'%mono)
out.append('int tot = 0; int bad = 0;'); out+=lines
out.append('"   layer N_1 generators (|B| = |A|+1) outside Q+box+F:", bad, "of", tot;')
out.append('quit;')
print('\n'.join(out))
