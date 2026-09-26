# regla261: truth test at q=9 of Fable open #3 type: new-class row 2 of (1)(N) contains F2(N-1) of (1,1).
# Membership z^2*F2 in K^unif_(1)(N) + (z^3), over F_3 (membership is field-independent), homogeneous, degBound = target degree.
# ESTIMATES (written before running): N=7: <=30 s, <=300 MB.  N=8: 1-5 min, <=1 GB (watchdog 1.2 GB / 600 s).
import itertools,sys
q=9
def gen(N,with_neg=True):
    n=N; mu=(1,); ell=1; f=n-1
    L=['ring r = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;'%n,
       'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
       'list X; int i; for (i = 1; i <= %d; i++) { X = insert(X, x(i), size(X)); }'%n,
       'ideal K = x(%d)^3;'%n]
    for j in range(1,n+1):
        L.append('K = K, x(%d)^%d;'%(j,q))
        if j%2==1 or j>=f+1: L.append('K = K, elv(X, %d);'%j)
    lam=list(mu)+[1]*f; conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
    dk=lambda k: sum(conj[n-k:]) if k>0 else 0
    for k in range(1,n):
        th=max(1,k-dk(k)+1)
        for S in itertools.combinations(range(1,n+1),k):
            lst='list(%s)'%(', '.join('x(%d)'%i for i in S))
            for rr in range(th,k+1): L.append('K = K, elv(%s, %d);'%(lst,rr))
    # family phi_jl = y_j^(q-1) e_{f-1}(y minus {j,l})
    for j in range(1,n+1):
        for l in range(1,n+1):
            if j==l: continue
            P=[i for i in range(1,n+1) if i not in (j,l)]
            L.append('K = K, x(%d)^%d * elv(list(%s), %d);'%(j,q-1,', '.join('x(%d)'%i for i in P),f-1))
    # layer N_0: x_A^(q-1) x_C, |B|=|A|>=1
    for a in range(1,n//2+1):
        for A in itertools.combinations(range(1,n+1),a):
            rest=[i for i in range(1,n+1) if i not in A]
            for B in itertools.combinations(rest,a):
                C=[i for i in rest if i not in B]
                L.append('K = K, %s;'%('*'.join(['x(%d)^%d'%(i,q-1) for i in A]+['x(%d)'%i for i in C])))
    # target: child (1,1)(N-1) on letters 1..N-1, f' = N-1-2 ; F2_{12;34} = (x1 x2)^(q-2) e_{f'-1}(child minus {3,4})
    fp=N-3; child=list(range(1,N)); V=[i for i in child if i not in (3,4)]
    Vs='list(%s)'%(', '.join('x(%d)'%i for i in V))
    T='x(%d)^2 * (x(1)*x(2))^%d * elv(%s, %d)'%(N,q-2,Vs,fp-1)
    Tn='x(%d)^2 * (x(1)*x(2))^%d * elv(%s, %d)'%(N,q-2,Vs,fp-2)
    Tr1='x(%d)^1 * (x(1)*x(2))^%d * elv(%s, %d)'%(N,q-2,Vs,fp-1)
    D=2+2*(q-2)+fp-1
    L.append('degBound = %d; ideal SK = std(K); degBound = 0;'%D)
    L.append('"N=%d target deg %d: z^2*F2 in K+(z^3):", reduce(%s, SK) == 0, "; neg control z^2*(x1x2)^(q-2)e_{f-2}:", reduce(%s, SK) == 0, "; row-1 control z*F2:", reduce(%s, SK) == 0, "; secs", timer - t0;'%(N,D,T,Tn,Tr1))
    L.append('quit;')
    return '\n'.join(L)
N=int(sys.argv[1]); open(sys.argv[2],'w').write(gen(N))
