# cert12.py — Fable 12: the auditor's certifier (grepy_casilla_verdadera.py) generalised to any q = 3^v, plus the
# ell = 2 law test: S2 := (y_c^2, y_a^(q-2)) * D_{j;cd},  D_{j;cd} := y_j^(q-2) e_{f-1}(y minus {c,d}).
# Usage: python3 cert12.py MU N Q [law] [shownew] [db=K] > cell.sing ; zsh grepy_vigia.sh cell.log 'Singular -q cell.sing'
import sys, itertools
def script(mu, n, q, law=False, shownew=False, db=0, g3=False):
    ell=len(mu); M=sum(mu); f=n-M
    anch=[]
    for i,m in enumerate(mu): anch += ['a^%d'%i]*m
    L=[]
    L.append('ring r = (%d,a), (x(1..%d), t), dp;'%(q,n))
    L.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list w = delete(vl, size(vl)); return(elv(w, k) + vl[size(vl)] * elv(w, k-1)); }')
    L.append('list X; int p; for (p = 1; p <= %d; p++) { X = insert(X, x(p), size(X)); }'%n)
    L.append('list SA = list(%s);'%(', '.join(anch)))
    L.append('ideal I; int j; int rr; poly g;')
    L.append('for (j = 1; j <= %d; j = j + 2) { g = 0; for (rr = 0; rr <= %d; rr++) { g = g + elv(SA, rr) * elv(X, j - rr); } I = I, homog(g, t); }'%(n+M, M))
    L.append('for (j = 1; j <= %d; j++) { I = I, x(j)^%d - x(j)*t^%d; }'%(n,q,q-1))
    L.append('degBound = %d; int t0 = timer; ideal G = std(I); degBound = 0;'%db)
    L.append('ideal T; int i; poly h; for (i = 1; i <= size(G); i++) { h = G[i]; while ((h != 0) && (subst(h, t, 0) == 0)) { h = h / t; } T = T, subst(h, t, 0); }')
    L.append('ideal K = t; for (j = 1; j <= %d; j++) { K = K, x(j)^%d; if ((j mod 2 == 1) || (j >= %d)) { K = K, elv(X, j); } }'%(n,q,n-M+1))
    lam=list(mu)+[1]*f
    conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
    def dk(k): return sum(conj[n-k:]) if k>0 else 0
    for k in range(1,n):
        th=max(1,k-dk(k)+1)
        if th<=k:
            for Ss in itertools.combinations(range(1,n+1),k):
                lst='list(%s)'%(', '.join('x(%d)'%i for i in Ss))
                for r in range(th,k+1): L.append('K = K, elv(%s, %d);'%(lst,r))
    tt=f+ell-2
    L.append('int l; list P;')
    L.append('for (j = 1; j <= %d; j++) { for (l = 1; l <= %d; l++) { if (j != l) { P = list(); for (p = 1; p <= %d; p++) { if ((p != j) && (p != l)) { P = insert(P, x(p), size(P)); } }'%(n,n,n))
    L.append('  h = 0; for (i = 0; i <= %d; i++) { h = h + x(j)^(%d + i) * elv(P, %d - i); } K = K, h; } } }'%(ell-1,q-ell,tt))
    if mu[0]>=2 or ell==1:
        w=mu[0]-1
        for a in range(0,n+1):
            b=a+w
            if b<1 or a+b>n: continue
            for A in itertools.combinations(range(1,n+1),a):
                rest=[i for i in range(1,n+1) if i not in A]
                for B in itertools.combinations(rest,b):
                    C=[i for i in rest if i not in B]
                    mono='*'.join(['x(%d)^%d'%(i,q-1) for i in A]+['x(%d)'%i for i in C]) or '1'
                    L.append('K = K, %s;'%mono)
    L.append('ideal SK = std(K); ideal ST = std(T + ideal(t));')
    L.append('int kin = 1; for (i = 1; i <= size(K); i++) { if (reduce(K[i], ST) != 0) { kin = 0; } }')
    L.append('int fib = %d;'%0)
    L.append('"RESULT q=%d mu=%s n=%d f=%d: vdim(unifK) =", vdim(SK), " vdim(tops) =", vdim(ST), " K<=tops:", kin, " sec:", timer - t0;'%(q,str(tuple(mu)),n,f))
    L.append('ideal N; for (i = 1; i <= size(T); i++) { h = reduce(T[i], SK); if (h != 0) { N = N, h; } } N = simplify(N, 2);')
    L.append('ideal M2 = K; ideal SM = SK; ideal NEW; for (i = 1; i <= size(N); i++) { if (reduce(N[i], SM) != 0) { NEW = NEW, N[i]; M2 = M2, N[i]; SM = std(M2); } } NEW = simplify(NEW, 2);')
    L.append('string dg = ""; for (i = 1; i <= size(NEW); i++) { dg = dg + string(deg(NEW[i])) + " "; }')
    L.append('"  NEW beyond K:", size(NEW), " degrees:", dg;')
    if shownew:
        L.append('for (i = 1; i <= size(NEW); i++) { "   NEW", i, "deg", deg(NEW[i]), "terms", size(NEW[i]); NEW[i]; }')
    if law and ell==2:
        # S2 members: y_c^2 D_{j;cd} (ordered c,d) and y_a^(q-2) D_{j;cd}
        L.append('ideal S2; int aa; int cc; int dd; int nsq = 0; int nsqin = 0; int nhv = 0; int nhvin = 0; list V2; poly Dd;')
        L.append('for (j = 1; j <= %d; j++) { for (cc = 1; cc <= %d; cc++) { for (dd = 1; dd <= %d; dd++) { if ((j != cc) && (j != dd) && (cc < dd)) {'%(n,n,n))
        L.append('  V2 = list(); for (p = 1; p <= %d; p++) { if ((p != cc) && (p != dd)) { V2 = insert(V2, x(p)); } }'%n)
        L.append('  Dd = x(j)^%d * elv(V2, %d);'%(q-2,f-1))
        L.append('  h = x(cc)^2 * Dd; nsq++; if (reduce(h, ST) == 0) { nsqin++; } S2 = S2, h; h = x(dd)^2 * Dd; nsq++; if (reduce(h, ST) == 0) { nsqin++; } S2 = S2, h;')
        L.append('  for (aa = 1; aa <= %d; aa++) { if ((aa != j) && (aa != cc) && (aa != dd)) { h = x(aa)^%d * Dd; nhv++; if (reduce(h, ST) == 0) { nhvin++; } S2 = S2, h; } } } } } }'%(n,q-2))
        L.append('ideal SKS = std(K + S2); int okS = 1; for (i = 1; i <= size(T); i++) { if (reduce(T[i], SKS) != 0) { okS = 0; } }')
        L.append('int redS = 1; for (i = 1; i <= size(S2); i++) { if (reduce(S2[i], SK) != 0) { redS = 0; } }')
        L.append('"  LAW y_c^2 D:", nsqin, "/", nsq, " y_a^(q-2) D:", nhvin, "/", nhv, " in tops ; vdim(K+S2) =", vdim(SKS), " ; K+S2 contains tops:", okS, " ; S2 inside unifK (redundant):", redS;')
    if g3:
        # (1,1) tower r = 3: G3(A;B) = x_A^(q-2) e_{n-4}(y minus B)
        L.append('ideal G3; int n3 = 0; int n3in = 0;')
        for A in itertools.combinations(range(1,n+1),3):
            rest=[i for i in range(1,n+1) if i not in A]
            for B in itertools.combinations(rest,3):
                V=[i for i in range(1,n+1) if i not in B]
                L.append('h = (%s)^%d * elv(list(%s), %d); n3++; if (reduce(h, ST) == 0) { n3in++; } G3 = G3, h;'%('*'.join('x(%d)'%i for i in A),q-2,', '.join('x(%d)'%i for i in V),n-4))
        L.append('int red3 = 1; for (i = 1; i <= size(G3); i++) { if (reduce(G3[i], SKS) != 0) { red3 = 0; } }')
        L.append('"  G3:", n3in, "/", n3, " in tops ; G3 inside K+S2 (redundant):", red3;')
    L.append('"  total sec:", timer - t0;')
    L.append('quit;')
    return '\n'.join(L)
if __name__=='__main__':
    mu=tuple(int(x) for x in sys.argv[1].split(',')); n=int(sys.argv[2]); q=int(sys.argv[3])
    opts=sys.argv[4:]
    db=0
    for o in opts:
        if o.startswith('db='): db=int(o[3:])
    print(script(mu,n,q,law='law' in opts,shownew='shownew' in opts,db=db,g3='g3' in opts))
