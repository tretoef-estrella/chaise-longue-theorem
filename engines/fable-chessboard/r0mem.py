# row 0 of K^unif_(1,1)(n) (= substitution z = 0) contains the child (1)(n-1) layer generator (ab)^(q-1) x_C with |B| = 2 ?
import itertools, sys
n, q = int(sys.argv[1]), int(sys.argv[2]); m = n-1
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % m,
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal K = 0;']
X = list(range(1, m+1))
for j in X:
    L.append('K = K, x(%d)^%d;' % (j, q))
    if j % 2 == 1 or j >= n-1: L.append('K = K, elv(%s, %d);' % (lst(X), j))   # e_j(y,z)|z=0 = e_j(y)
for j in X:
    for l in X:
        if j != l: L.append('K = K, x(%d)^%d * elv(%s, %d);' % (j, q-1, lst([i for i in X if i not in (j, l)]), n-3))  # phi_jl|z=0
    L.append('K = K, x(%d)^%d * elv(%s, %d);' % (j, q-2, lst(X), n-2))   # phi_{j z}|z=0
tgt = 'x(1)^%d*x(2)^%d*%s' % (q-1, q-1, '*'.join('x(%d)' % i for i in range(5, m+1)) or '1')
D = 2*(q-1)+m-4
L.append('degBound = %d; ideal SK = std(K); degBound = 0;' % D)
L.append('"row0 (1,1)(%d) q=%d: (x1x2)^(q-1) x_C (absent 3,4) in K|z=0:", reduce(%s, SK) == 0, "; secs", timer-t0;' % (n, q, tgt))
L.append('quit;')
open(sys.argv[3], 'w').write('\n'.join(L))
