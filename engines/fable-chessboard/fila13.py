# mission 13, E3: Singular memberships over F_3 (field-independent), homogeneous, degBound = target degree.
# mode 'row2':  z^2*G_r(A;B)(n) in K^unif_(1)(n+1) + (z^3)   [controls: z*G_r, and z^2 * x_A^{q-2} e_{n-r-2}(y\B)]
# mode 'content': G_r(A;B)(n) in B_n + (phi_jl) ,  B_n = (e_k : k odd or k >= n-1) + box + N_0(n), phi_jl = y_j^{q-2} e_{n-2}(y\l)
import itertools, sys
mode, N, q, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
def head(nv):
    return ['ring rr = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % nv,
            'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }']
def K1(n, L, Kname='K'):   # K^unif_(1)(n) on letters 1..n (Q incl. Tanisaki, box, family phi^(1), layer N_0)
    f = n-1; X = list(range(1, n+1))
    for j in X:
        L.append('%s = %s, x(%d)^%d;' % (Kname, Kname, j, q))
        if j % 2 == 1 or j >= f+1: L.append('%s = %s, elv(%s, %d);' % (Kname, Kname, lst(X), j))
    lam = [1]+[1]*f; conj = [sum(1 for x in lam if x >= i) for i in range(1, n+1)]
    dk = lambda k: sum(conj[n-k:]) if k > 0 else 0
    for k in range(1, n):
        th = max(1, k-dk(k)+1)
        for S in itertools.combinations(X, k):
            for rr_ in range(th, k+1): L.append('%s = %s, elv(%s, %d);' % (Kname, Kname, lst(S), rr_))
    for j in X:
        for l in X:
            if j != l:
                L.append('%s = %s, x(%d)^%d * elv(%s, %d);' % (Kname, Kname, j, q-1, lst([i for i in X if i not in (j, l)]), f-1))
    layer(n, X, L, Kname)
def layer(n, X, L, Kname):
    for a in range(1, n//2+1):
        for A in itertools.combinations(X, a):
            rest = [i for i in X if i not in A]
            for B in itertools.combinations(rest, a):
                C = [i for i in rest if i not in B]
                L.append('%s = %s, %s;' % (Kname, Kname, '*'.join(['x(%d)^%d' % (i, q-1) for i in A]+['x(%d)' % i for i in C] or ['1'])))
def Gr(n, extra=0):
    A = list(range(1, r+1)); B = list(range(r+1, 2*r+1))
    rest = [i for i in range(1, n+1) if i not in B]
    return '%s * elv(%s, %d)' % ('*'.join('x(%d)^%d' % (i, q-2) for i in A), lst(rest), n-r-1-extra), r*(q-2)+n-r-1-extra
if mode == 'row2':
    n = N-1; L = head(N); L.append('ideal K = x(%d)^3;' % N); K1(N, L)
    g, d = Gr(n); gn, dn = Gr(n, 1)
    D = d+2
    L.append('degBound = %d; ideal SK = std(K); degBound = 0;' % D)
    L.append('"row2 (1)(%d) >= G_%d(%d), q=%d: z^2*G in K+(z^3):", reduce(x(%d)^2*%s, SK) == 0, "; control z*G:", reduce(x(%d)*%s, SK) == 0, "; control z^2*x_A^(q-2)e_(n-r-2):", reduce(x(%d)^2*%s, SK) == 0, "; secs", timer-t0;' % (N, r, n, q, N, g, N, g, N, gn))
elif mode == 'content':
    n = N; X = list(range(1, n+1)); L = head(n); L.append('ideal K = 0;')
    for j in X:
        L.append('K = K, x(%d)^%d;' % (j, q))
        if j % 2 == 1 or j >= n-1: L.append('K = K, elv(%s, %d);' % (lst(X), j))
    layer(n, X, L, 'K')
    L.append('ideal KB = K;')
    for j in X:
        for l in X:
            if j != l: L.append('K = K, x(%d)^%d * elv(%s, %d);' % (j, q-2, lst([i for i in X if i != l]), n-2))
    g, d = Gr(n)
    L.append('degBound = %d; ideal SK = std(K); ideal SB = std(KB); degBound = 0;' % d)
    L.append('"content n=%d q=%d r=%d: G in B:", reduce(%s, SB) == 0, "; G in B+(phi):", reduce(%s, SK) == 0, "; secs", timer-t0;' % (n, q, r, g, g))
L.append('quit;')
open(sys.argv[5], 'w').write('\n'.join(L))
