# z^(q-2) * y_j^(q-2) e_{n-4}(y\l)  in  K^unif_(2,1)(n+1) + (z^(q-1)) ?  (Singular, degree-bounded, over F_3); j = x(1), l = x(2), z = x(n+1)
import itertools, sys
q = int(sys.argv[1]); n = int(sys.argv[2]); out = sys.argv[3]
N = n+1; Y = list(range(1, N+1)); f = N-3
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % N,
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal K = x(%d)^%d;' % (N, q-1)]
for i in Y:
    L.append('K = K, x(%d)^%d;' % (i, q))
    if i % 2 == 1 or i >= f+1: L.append('K = K, elv(%s, %d);' % (lst(Y), i))
lam = [2]+[1]*(1+f); conj = [sum(1 for x in lam if x >= i) for i in range(1, N+1)]
dk = lambda k: sum(conj[N-k:]) if k > 0 else 0
for k in range(1, N):
    th = max(1, k-dk(k)+1)
    for S in itertools.combinations(Y, k):
        for r_ in range(th, k+1): L.append('K = K, elv(%s, %d);' % (lst(S), r_))
for a in range(0, N):
    for A in itertools.combinations(Y, a):
        rest = [i for i in Y if i not in A]
        if a+1 > len(rest): continue
        for B in itertools.combinations(rest, a+1):
            C = [i for i in rest if i not in B]
            L.append('K = K, %s;' % ('*'.join(['x(%d)^%d' % (i, q-1) for i in A]+['x(%d)' % i for i in C]) or '1'))
for a in Y:
    for b in Y:
        if a != b: L.append('K = K, x(%d)^%d * elv(%s, %d);' % (a, q-2, lst([i for i in Y if i != b]), f))
tgt = 'x(%d)^%d * x(1)^%d * elv(%s, %d)' % (N, q-2, q-2, lst([i for i in range(1, n+1) if i != 2]), n-4)
L.append('degBound = %d; ideal S1 = std(K); degBound = 0;' % (2*q+n-8))
L.append('"(2,1)(%d) q=%d: z^(q-2) phi^(2)_jl in K+(z^(q-1)):", reduce(%s, S1) == 0, "; control z^(q-3) phi:", reduce(%s, S1) == 0, "; secs", timer-t0;' % (N, q, tgt, tgt.replace('x(%d)^%d' % (N, q-2), 'x(%d)^%d' % (N, q-3), 1)))
L.append('quit;')
open(out, 'w').write('\n'.join(L))
