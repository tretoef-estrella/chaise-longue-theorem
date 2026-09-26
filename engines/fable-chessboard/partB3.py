# PART B, |A| = 2 layer generators of (2,1^{L-2}) at f = 2, q-free (Fable 12):
# test (a a')^{m+ell-1} x_C  in  Q''  + (a^m Psi_{a,beta}, a'^m Psi_{a',beta}) + (a^{m+ell}, a'^{m+ell})   over F_3,
# Psi_{jl} = sum_{i<ell} y_j^i e_{ell-i}(y minus {j,l}),  Q'' = q-free part of Q_mu(n).  One m0 => all m >= m0 (multiply by (aa')^k).
import sys, itertools
L=int(sys.argv[1]); M0=int(sys.argv[2]); ell=L-1; n=L+2; f=2; mu=[2]+[1]*(ell-1)
v=['a','ap','b1','b2','b3']+['c%d'%i for i in range(1,L-2)]
out=['ring r = 3, (%s), dp;'%(','.join(v))]
out.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }')
Xs=lambda S: 'list(%s)'%(','.join(S))
Q=['elv(%s,%d)'%(Xs(v),j) for j in range(1,n+1) if j%2==1 or j>=f+1]
lam=mu+[1]*f; conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
def dk(k): return sum(conj[n-k:]) if k>0 else 0
for k in range(1,n):
    for Ss in itertools.combinations(v,k):
        for rr in range(max(1,k-dk(k)+1),k+1): Q.append('elv(%s,%d)'%(Xs(Ss),rr))
def Psi(j,l):
    P=[w for w in v if w not in (j,l)]
    return '(' + '+'.join('%s^%d*elv(%s,%d)'%(j,i,Xs(P),ell-i) for i in range(ell)) + ')'
C=v[5:]; xC='*'.join(C) if C else '1'
for m in range(1,M0+1):
    fam=['a^%d*%s'%(m,Psi('a',beta)) for beta in v if beta!='a']+['ap^%d*%s'%(m,Psi('ap',beta)) for beta in v if beta!='ap']
    out.append('ideal J = %s, %s, a^%d, ap^%d; ideal SJ = std(J); "L=%d m=%d: (a ap)^(m+ell-1) x_C in Q + a,ap-families + a,ap-box:", reduce((a*ap)^%d*%s, SJ) == 0;'%(', '.join(Q),', '.join(fam),m+ell,m+ell,L,m,m+ell-1,xC))
out.append('quit;')
print('\n'.join(out))
