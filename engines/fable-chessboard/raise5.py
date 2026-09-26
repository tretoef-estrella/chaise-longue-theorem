# mission 13, PART C: raise row q-2 of K^unif_(2,1)(7) vs the (2,2)(6) family. j = x(1), l = x(2), P = x(3..6), z = x(7).
import itertools, sys
q = int(sys.argv[1]); out = sys.argv[2]
n = 7; Y = list(range(1, 8)); y = list(range(1, 7)); z = 7
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..7)), dp; option(redSB); int t0 = timer;',
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal K = 0;']
def layer(X, w, name):
    for a in range(0, len(X)):
        for A in itertools.combinations(X, a):
            rest = [i for i in X if i not in A]
            b = a+w
            if b < 1 or b > len(rest): continue
            for B in itertools.combinations(rest, b):
                C = [i for i in rest if i not in B]
                L.append('%s = %s, %s;' % (name, name, '*'.join(['x(%d)^%d' % (i, q-1) for i in A]+['x(%d)' % i for i in C]) or '1'))
for j in Y:
    L.append('K = K, x(%d)^%d;' % (j, q))
for k in (1, 3, 5, 6, 7): L.append('K = K, elv(%s, %d);' % (lst(Y), k))
for S in itertools.combinations(Y, 6): L.append('K = K, %s;' % '*'.join('x(%d)' % i for i in S))
layer(Y, 1, 'K')
for a in Y:
    for b in Y:
        if a != b: L.append('K = K, x(%d)^%d * elv(%s, 4);' % (a, q-2, lst([i for i in Y if i != b])))
# child pieces (proved in row q-2, INFORME_12 4.2): Q_(2,2)(6) + box + N_1(6) on y
L.append('ideal Kc = 0;')
for j in y: L.append('Kc = Kc, x(%d)^%d;' % (j, q))
for k in (1, 3, 4, 5, 6): L.append('Kc = Kc, elv(%s, %d);' % (lst(y), k))
for S in itertools.combinations(y, 5):
    for rr_ in (4, 5): L.append('Kc = Kc, elv(%s, %d);' % (lst(S), rr_))
layer(y, 1, 'Kc')
L.append('ideal K1 = K, x(7)^%d;' % (q-1))
L.append('ideal K2 = K, x(7)^%d * Kc, x(7)^%d;' % (q-2, q-1))
L.append('ideal K3 = K, x(7)^%d;' % (q-2))
tgt = 'x(7)^%d * x(1)^%d * elv(%s, 2)' % (q-2, q-2, lst([1, 3, 4, 5, 6]))
low = 'x(7)^%d * x(1)^%d * elv(%s, 3)' % (q-3, q-2, lst([1, 3, 4, 5, 6]))
D = 2*q-2
L.append('degBound = %d; ideal S1 = std(K1); ideal S2 = std(K2); ideal S3 = std(K3); degBound = 0;' % D)
L.append('"q=%d T1 z^(q-2)phi in K+(z^(q-1)):", reduce(%s, S1) == 0, "; T2 low in K+z^(q-2)Kc+(z^(q-1)):", reduce(%s, S2) == 0, "; T3 low in K+(z^(q-2)):", reduce(%s, S3) == 0, "; T1b z^(q-2)phi in K+z^(q-2)Kc+(z^(q-1)) [same as T1]:", reduce(%s, S2) == 0, "; secs", timer-t0;' % (q, tgt, low, low, tgt))
L.append('quit;')
open(out, 'w').write('\n'.join(L))
