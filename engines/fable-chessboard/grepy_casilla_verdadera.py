# grepy_casilla_verdadera.py — the auditor's CERTIFIER of the TRUE casilla gr I(W_mu(n)) at q = 9 (Grepy el Lector, 2026-09-23).
# Method: homogenize the fibre ideal (R_j, j odd; x_i^9 - x_i) with t, t LAST in dp, standard basis with degBound 40, divide each
# element by its largest power of t, set t = 0: these forms lie in gr I(W).  If their colength (vdim) equals the fibre |W_mu(n)|,
# they GENERATE gr I(W) exactly.  Then: the UNIFORM casilla K (minimal layer), vdim(K), the new generators beyond K (normal forms),
# and optional tests of the second family F2_{ab;cd} = (y_a y_b)^(q-E) * e_{f-1+D}(y minus {c,d}) for given E:D.
# Usage:  python3 grepy_casilla_verdadera.py MU N [E:D ...] > cell.sing ;  zsh grepy_vigia.sh cell.log 'Singular -q cell.sing'
#   e.g.  python3 grepy_casilla_verdadera.py 1,1 7 2:0 > c.sing      (MU as comma list; anchors a^0, a^1, a^2, a^3: one class each)
# Known costs (auditor, q = 9): (1,1) n=6: 0 s; (1,1) n=7: 18-24 s; (2,2) n=7: 40 s; (1,1,1) n=7: 50 s; (1,1) n=8: KILLED at 601 s.
import sys
def script(mu, n, fams, q=9):
    ell=len(mu); M=sum(mu); f=n-M
    anch=[]
    for i,m in enumerate(mu): anch += ['a^%d'%i]*m      # distinct classes: a^0, a^1, a^2, a^3 (a has order 8; -a^i = a^(i+4)). FIX: v1 used a^(2i), and a^4 = -1 is the class of 1
    L=[]
    L.append('ring r = (9,a), (x(1..%d), t), dp;'%n)
    L.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list w = delete(vl, size(vl)); return(elv(w, k) + vl[size(vl)] * elv(w, k-1)); }')
    L.append('list X; int p; for (p = 1; p <= %d; p++) { X = insert(X, x(p), size(X)); }'%n)
    L.append('list SA = list(%s);'%(', '.join(anch)))
    L.append('ideal I; int j; int rr; poly g;')
    L.append('for (j = 1; j <= %d; j = j + 2) { g = 0; for (rr = 0; rr <= %d; rr++) { g = g + elv(SA, rr) * elv(X, j - rr); } I = I, homog(g, t); }'%(n+M, M))
    L.append('for (j = 1; j <= %d; j++) { I = I, x(j)^%d - x(j)*t^%d; }'%(n,q,q-1))
    L.append('degBound = 40; int t0 = timer; ideal G = std(I); degBound = 0;')
    L.append('ideal T; int i; poly h; for (i = 1; i <= size(G); i++) { h = G[i]; while ((h != 0) && (subst(h, t, 0) == 0)) { h = h / t; } T = T, subst(h, t, 0); }')
    # uniform K
    L.append('ideal K = t; for (j = 1; j <= %d; j++) { K = K, x(j)^%d; if ((j mod 2 == 1) || (j >= %d)) { K = K, elv(X, j); } }'%(n,q,n-M+1))
    lam=list(mu)+[1]*f
    conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
    def dk(k): return sum(conj[n-k:]) if k>0 else 0
    L.append('list Y; int k2; int r2; intvec sub;')
    # Tanisaki proper subsets
    import itertools
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
    if mu[0]>=2:
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
    L.append('ideal SK = std(K); ideal SG = std(K + T); ideal ST = std(T + ideal(t));')
    L.append('int kin = 1; for (i = 1; i <= size(K); i++) { if (reduce(K[i], ST) != 0) { kin = 0; } }')
    L.append('"mu=%s n=%d f=%d: vdim(uniform K) =", vdim(SK), " vdim(tops alone) =", vdim(ST), " (= fibre means CERTIFIED gr I) ; K inside tops:", kin, " ; vdim(K + tops) =", vdim(SG), " ; seconds:", timer - t0;'%(str(tuple(mu)),n,f))
    L.append('ideal N; for (i = 1; i <= size(T); i++) { h = reduce(T[i], SK); if (h != 0) { N = N, h; } } N = simplify(N, 2);')
    L.append('ideal M2 = K; ideal SM = SK; ideal NEW; for (i = 1; i <= size(N); i++) { if (reduce(N[i], SM) != 0) { NEW = NEW, N[i]; M2 = M2, N[i]; SM = std(M2); } } NEW = simplify(NEW, 2);')
    L.append('"  new independent generators beyond K:", size(NEW); for (i = 1; i <= size(NEW) && i <= 40; i++) { "   deg", deg(NEW[i]), "terms", size(NEW[i]); NEW[i]; }')
    L.append('if (size(NEW) > 0) { "  example:"; NEW[1]; }')
    for (E,D) in fams:
        L.append('ideal F; int aa; int bb; int cc; int dd; int inG = 0; int tot = 0; list V2;')
        L.append('for (aa = 1; aa <= %d; aa++) { for (bb = aa+1; bb <= %d; bb++) { for (cc = 1; cc <= %d; cc++) { for (dd = cc+1; dd <= %d; dd++) {'%(n,n,n,n))
        L.append('  if ((cc != aa) && (cc != bb) && (dd != aa) && (dd != bb)) { V2 = list(); for (p = 1; p <= %d; p++) { if ((p != cc) && (p != dd)) { V2 = insert(V2, x(p)); } }'%n)
        L.append('    h = (x(aa)*x(bb))^%d * elv(V2, %d); tot++; if (reduce(h, SG) == 0) { inG++; } F = F, h; } } } } }'%(q-E, f-1+D))
        L.append('ideal SKF = std(K + F); int okF = 1; for (i = 1; i <= size(T); i++) { if (reduce(T[i], SKF) != 0) { okF = 0; } }')
        L.append('"  family (y_a y_b)^(q-%d) e_{f-1+%d}(y minus {c,d}):", inG, "of", tot, "in G ; vdim(K + F) =", vdim(SKF), "; K + F == G ?", okF;'%(E,D))
        L.append('kill F; kill aa; kill bb; kill cc; kill dd; kill inG; kill tot; kill V2; kill SKF; kill okF;')
    L.append('quit;')
    return '\n'.join(L)
if __name__=='__main__':
    mu=tuple(int(x) for x in sys.argv[1].split(',')); n=int(sys.argv[2])
    fams=[tuple(int(x) for x in s.split(':')) for s in sys.argv[3:]]
    print(script(mu,n,fams))
