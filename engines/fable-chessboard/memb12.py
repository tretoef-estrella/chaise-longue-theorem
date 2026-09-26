# memb12.py — Fable 12: membership of named forms in the CERTIFIED gr I(W_mu(n)) (tops of the t-homogenised standard basis).
# Usage: python3 memb12.py MU N Q tests.txt > m.sing ; tests.txt lines "name := singular_poly" (letters x(1)..x(n), proc elv, e(S,k) via elv(list(..),k))
import sys
mu=tuple(int(x) for x in sys.argv[1].split(',')); n=int(sys.argv[2]); q=int(sys.argv[3]); tests=open(sys.argv[4]).read().strip().splitlines()
M=sum(mu); anch=[]
for i,m in enumerate(mu): anch += ['a^%d'%i]*m
L=['ring r = (%d,a), (x(1..%d), t), dp;'%(q,n),
 'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list w = delete(vl, size(vl)); return(elv(w, k) + vl[size(vl)] * elv(w, k-1)); }',
 'list X; int p; for (p = 1; p <= %d; p++) { X = insert(X, x(p), size(X)); }'%n,
 'list SA = list(%s);'%(', '.join(anch)), 'ideal I; int j; int rr; poly g;',
 'for (j = 1; j <= %d; j = j + 2) { g = 0; for (rr = 0; rr <= %d; rr++) { g = g + elv(SA, rr) * elv(X, j - rr); } I = I, homog(g, t); }'%(n+M, M),
 'for (j = 1; j <= %d; j++) { I = I, x(j)^%d - x(j)*t^%d; }'%(n,q,q-1),
 'int t0 = timer; ideal G = std(I);',
 'ideal T; int i; poly h; for (i = 1; i <= size(G); i++) { h = G[i]; while ((h != 0) && (subst(h, t, 0) == 0)) { h = h / t; } T = T, subst(h, t, 0); }',
 'ideal ST = std(T + ideal(t)); "mu=%s n=%d q=%d vdim(tops) =", vdim(ST), " sec", timer-t0;'%(str(mu),n,q)]
for ln in tests:
    if ':=' not in ln: continue
    name,pol=ln.split(':=',1)
    L.append('h = %s; "  %-40s deg", deg(h), " in gr I:", reduce(h, ST) == 0;'%(pol.strip(),name.strip()))
L.append('quit;')
print('\n'.join(L))
