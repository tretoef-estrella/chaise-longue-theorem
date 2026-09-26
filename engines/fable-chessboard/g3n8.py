# PART F: G_3(123;456)(8) in K^unif_(1,1)(8) + (F2) ?  q = 9, 8 variables, over F_3, homogeneous, degBound = deg G_3 = 25.
import itertools, sys
q = 9; n = 8; X = list(range(1, n+1)); out = sys.argv[1]
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % n,
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal K = 0;']
for j in X:
    L.append('K = K, x(%d)^%d;' % (j, q))
    if j % 2 == 1 or j >= n-1: L.append('K = K, elv(%s, %d);' % (lst(X), j))
for j in X:
    for l in X:
        if j != l: L.append('K = K, x(%d)^%d * elv(%s, %d);' % (j, q-2, lst([i for i in X if i != l]), n-2))
for a, b in itertools.combinations(X, 2):
    rest = [i for i in X if i not in (a, b)]
    for c, d in itertools.combinations(rest, 2):
        L.append('K = K, (x(%d)*x(%d))^%d * elv(%s, %d);' % (a, b, q-2, lst([i for i in X if i not in (c, d)]), n-3))
tgt = '(x(1)*x(2)*x(3))^%d * elv(%s, %d)' % (q-2, lst([1, 2, 3, 7, 8]), n-4)
D = 3*(q-2)+n-4
L.append('degBound = %d; ideal SK = std(K); degBound = 0;' % D)
L.append('"G_3(8) in K^unif_(1,1)(8)+(F2), q=9:", reduce(%s, SK) == 0, "; secs", timer-t0;' % tgt)
L.append('quit;')
open(out, 'w').write('\n'.join(L))
