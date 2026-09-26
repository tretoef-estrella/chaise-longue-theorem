# regla262_mapa.py — Grepy el Lector, MISION 88. Where does row k=5 need a corrected casilla?
# vdim(K^unif_mu(n)) over F_3 (full std, dp) versus |W_mu(n)| at q=9 (EGF). vdim > |W| => uniform too small => correction forced.
# K^unif = Q_mu(n) (odd e_j, e_j for j>=f+1, Tanisaki e_r(x_S) r > |S|-d_|S|(lambda)) + box + layer N_{mu1-1} (omitted for (1^l), l>=2) + family phi^(l).
import sys, itertools
def gen(mu, n, q):
    l = len(mu); f = n - sum(mu)
    L = ['ring r = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % n,
         'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
         'list X; int i; for (i = 1; i <= %d; i++) { X = insert(X, x(i), size(X)); }' % n, 'ideal K = x(1)^%d;' % q]
    for j in range(1, n + 1):
        L.append('K = K, x(%d)^%d;' % (j, q))
        if j % 2 == 1 or j >= f + 1: L.append('K = K, elv(X, %d);' % j)
    lam = list(mu) + [1] * f; conj = [sum(1 for x in lam if x >= i) for i in range(1, n + 1)]
    dk = lambda k: sum(conj[n - k:]) if k > 0 else 0
    for k in range(1, n):
        th = max(1, k - dk(k) + 1)
        if th > k: continue
        for S in itertools.combinations(range(1, n + 1), k):
            for rr in range(th, k + 1): L.append('K = K, elv(list(%s), %d);' % (', '.join('x(%d)' % i for i in S), rr))
    if not (l >= 2 and mu[0] == 1):
        w = mu[0] - 1
        for a in range(0, n + 1):
            for A in itertools.combinations(range(1, n + 1), a):
                rest = [i for i in range(1, n + 1) if i not in A]
                bmax = min(a + w, len(rest))
                if bmax < 1: continue
                for B in itertools.combinations(rest, bmax):
                    C = [i for i in rest if i not in B]
                    L.append('K = K, %s;' % ('*'.join(['x(%d)^%d' % (i, q - 1) for i in A] + ['x(%d)' % i for i in C]) or '1'))
    for j in range(1, n + 1):
        for ll in range(1, n + 1):
            if j == ll: continue
            P = 'list(%s)' % ', '.join('x(%d)' % i for i in range(1, n + 1) if i not in (j, ll))
            L.append('K = K, x(%d)^%d * (%s);' % (j, q - l, ' + '.join('x(%d)^%d * elv(%s, %d)' % (j, i, P, f + l - 2 - i) for i in range(l))))
    L.append('ideal SK = std(K); "mu=%s n=%d q=%d vdim(K^unif) =", vdim(SK), " secs", timer - t0;' % (str(mu).replace(' ', ''), n, q))
    L.append('quit;'); return '\n'.join(L)
mu = tuple(int(x) for x in sys.argv[1].split(',')); n = int(sys.argv[2]); q = int(sys.argv[3]); open(sys.argv[4], 'w').write(gen(mu, n, q))
