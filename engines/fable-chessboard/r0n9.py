# PART F necessity test (post hoc): row 0 of K^unif_(1,1)(9) + (F2), i.e. its substitution z = 0 (8 variables),
# contains the child (1)(8)'s floor-3 layer generator (x1x2x3)^(q-1) x7 x8 (absent 4,5,6)?  Prediction (F_3 rank): NO.
import itertools, sys
q = 9; n = 9; m = 8; X = list(range(1, m+1)); out = sys.argv[1]
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % m,
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal K = 0;']
for j in X:
    L.append('K = K, x(%d)^%d;' % (j, q))
    if j % 2 == 1 or j >= n-1: L.append('K = K, elv(%s, %d);' % (lst(X), j))
for j in X:   # phi_jl|z=0 (l != z), phi_jz|z=0
    for l in X:
        if j != l: L.append('K = K, x(%d)^%d * %s;' % (j, q-1, '*'.join('x(%d)' % i for i in X if i not in (j, l))))
    L.append('K = K, x(%d)^%d * elv(%s, %d);' % (j, q-2, lst(X), n-2))
for a, b in itertools.combinations(X, 2):   # F2|z=0: z not in {a,b,c,d}: (ab)^(q-1) x_rest ; z in {c,d}: (ab)^(q-2) e_{n-3}(y \\ c)
    rest = [i for i in X if i not in (a, b)]
    for c, d in itertools.combinations(rest, 2):
        L.append('K = K, (x(%d)*x(%d))^%d * %s;' % (a, b, q-1, '*'.join('x(%d)' % i for i in X if i not in (a, b, c, d))))
    for c in rest:
        L.append('K = K, (x(%d)*x(%d))^%d * elv(%s, %d);' % (a, b, q-2, lst([i for i in X if i != c]), n-3))
tgt = '(x(1)*x(2)*x(3))^%d * x(7) * x(8)' % (q-1)
L.append('degBound = %d; ideal SK = std(K); degBound = 0;' % (3*(q-1)+2))
L.append('"row0 (1,1)(9) with F2, q=9: floor-3 layer (x1x2x3)^(q-1)x7x8 in K|z=0:", reduce(%s, SK) == 0, "; secs", timer-t0;' % tgt)
L.append('quit;')
open(out, 'w').write('\n'.join(L))
