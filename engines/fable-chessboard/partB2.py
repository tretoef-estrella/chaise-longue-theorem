# PART B, q-free form (Fable 12).  Pi_L := x_C * sum_{m=0}^{L-1} (-1)^m pt_m a^{L-1-m}  -  (-1)^{L-1} p_{L-1}(b) prod_{x in C}(a+x),
# pt_0 = 1, pt_m = b1^m + b2^m.  Claim A (exact, mod a^q):  a^{q-L} Pi_L == sum_i h_{L-2}(a,-b_{3-i}) phi_{a b_i} - a^{q-1} x_C.
# Claim B (q-free, over F_3):  a^{m0} Pi_L  in  (e_1, e_3, e_4, ..., e_n) + (x_{[n]\beta}) + (a^{m0+L})  for the printed m0.
import sys
L=int(sys.argv[1]); M0=int(sys.argv[2]); n=L+2
v=['a','b1','b2']+['c%d'%i for i in range(1,L)]
out=['ring r = 3, (%s), dp;'%(','.join(v))]
out.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }')
X='list(%s)'%(','.join(v)); C=v[3:]; xC='*'.join(C)
pt=['1']+['(b1^%d+b2^%d)'%(m,m) for m in range(1,L)]
Pi='%s*(%s) - (%d)*(b1^%d+b2^%d)*%s'%(xC,'+'.join('(%d)*%s*a^%d'%((-1)**m,pt[m],L-1-m) for m in range(L)),(-1)**(L-1),L-1,L-1,'*'.join('(a+%s)'%c for c in C))
out.append('poly PI = %s;'%Pi)
gens=['elv(%s,%d)'%(X,j) for j in range(1,n+1) if j%2==1 or j>=3]
gens+=['*'.join(w for w in v if w!=beta) for beta in v]
for m0 in range(0,M0+1):
    out.append('ideal J%d = %s, a^%d; ideal S%d = std(J%d); "L=%d m0=%d: a^m0 * Pi_L in (e_1,e_3,e_>=3) + (x_[n]minus beta) + (a^(m0+L)):", reduce(a^%d*PI, S%d) == 0;'%(m0,', '.join(gens),m0+L,m0,m0,L,m0,m0,m0))
# claim A check at q = 9, 27 (exact mod a^q) in a ring over F_3 (all coefficients are integers)
for q in (9,27,81):
    ell=L-1
    P1=['b2']+C; P2=['b1']+C
    def phi(P): return '(' + '+'.join('a^%d*elv(list(%s),%d)'%(q-ell+i,','.join(P),ell-i) for i in range(ell)) + ')'
    def h(D,u,w): return '(' + '+'.join('(%s)^%d*(%s)^%d'%(u,i,w,D-i) for i in range(D+1)) + ')' if D>=0 else '0'
    rhs='%s*%s + %s*%s - a^%d*%s'%(h(L-2,'a','-b2'),phi(P1),h(L-2,'a','-b1'),phi(P2),q-1,xC)
    out.append('ideal Aq = a^%d; ideal SAq = std(Aq); "  claim A at q=%d:", reduce(a^%d*PI - (%s), SAq) == 0;'%(q,q,q-L,rhs))
out.append('quit;')
print('\n'.join(out))
