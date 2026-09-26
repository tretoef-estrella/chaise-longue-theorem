# row0.py — Fable 12: ROW 0 of the (1,1) casilla at n (substitution z = x_n = 0, Theorem C) vs the child (1) at n-1.
# K(n) = Q + box + F + S2 (+ G3 if asked); child K_(1)(n-1) = Q_(1) + box + N_0 + F_(1). Usage: python3 row0.py n q [g3] > f.sing
import sys, itertools
n=int(sys.argv[1]); q=int(sys.argv[2]); g3='g3' in sys.argv[3:]
m=n-1; f=n-2
L=['ring r = (%d,a), (x(1..%d)), dp;'%(q,m)]
L.append('proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list w = delete(vl, size(vl)); return(elv(w, k) + vl[size(vl)] * elv(w, k-1)); }')
def lst(S): return 'list(%s)'%(', '.join('x(%d)'%i for i in S if i<=m)) if any(i<=m for i in S) else 'list()'
def E(S,k):  # e_k of letters S (letter n = z is 0)
    S=[i for i in S if i<=m]
    if k<0 or k>len(S): return '0'
    if k==0: return '1'
    return 'elv(%s, %d)'%(lst(S),k)
def X(i): return '0' if i==n else 'x(%d)'%i
L.append('int t0 = timer; ideal K;')
allv=list(range(1,n+1))
for j in range(1,n+1):
    if j%2==1 or j>=f+1: L.append('K = K, %s;'%E(allv,j))
for i in range(1,m+1): L.append('K = K, x(%d)^%d;'%(i,q))
# first family phi_jl = y_j^(q-2) e_f(y minus l)
for j in allv:
    for l in allv:
        if j!=l and j!=n: L.append('K = K, %s^%d * %s;'%(X(j),q-2,E([i for i in allv if i!=l],f)))
# S2: D_{j;cd} = y_j^(q-2) e_{f-1}(y minus {c,d}); multipliers y_c^2, y_d^2, y_a^(q-2)
for j in allv:
    if j==n: continue
    for c,d in itertools.combinations([i for i in allv if i!=j],2):
        D='%s^%d * %s'%(X(j),q-2,E([i for i in allv if i not in (c,d)],f-1))
        for mm in [c,d]:
            if mm!=n: L.append('K = K, %s^2 * %s;'%(X(mm),D))
        for a in allv:
            if a not in (j,c,d) and a!=n: L.append('K = K, %s^%d * %s;'%(X(a),q-2,D))
if g3:
    for A in itertools.combinations([i for i in allv if i!=n],3):
        for B in itertools.combinations([i for i in allv if i not in A],3):
            L.append('K = K, (%s)^%d * %s;'%('*'.join('x(%d)'%i for i in A),q-2,E([i for i in allv if i not in B],n-4)))
L.append('K = simplify(K, 2); ideal SK = std(K);')
L.append('"ROW0 of (1,1) at n=%d, q=%d%s: vdim =", vdim(SK), " sec", timer - t0;'%(n,q,' + G3' if g3 else ''))
# child (1) at m: Q_(1) = e_j j odd or j >= m; box; N_0: x_A^(q-1) x_C, |A| = |B| >= 1; F_(1) = y_j^(q-1) e_{m-2}(y minus {j,l}) (in N_0)
ch=list(range(1,m+1))
L.append('int bad = 0; int tot = 0; list badA = list(0,0,0,0,0);')
for j in ch:
    if j%2==1 or j>=m: L.append('tot++; if (reduce(%s, SK) != 0) { bad++; "  missing e_%d"; }'%(E(ch,j),j))
for r in range(1,m//2+1):
    cnt=0
    for A in itertools.combinations(ch,r):
        rest=[i for i in ch if i not in A]
        for B in itertools.combinations(rest,r):
            C=[i for i in rest if i not in B]
            mono='*'.join(['x(%d)^%d'%(i,q-1) for i in A]+['x(%d)'%i for i in C])
            L.append('tot++; if (reduce(%s, SK) != 0) { bad++; badA[%d] = badA[%d] + 1; }'%(mono,r,r))
for j in ch:
    for l in ch:
        if j!=l: L.append('tot++; if (reduce(x(%d)^%d * %s, SK) != 0) { bad++; }'%(j,q-1,E([i for i in ch if i not in (j,l)],m-2)))
L.append('"  child (1) at %d generators missing from the row:", bad, "of", tot, " ; missing layer by |A| = 1,2,3:", badA[1], badA[2], badA[3];'%m)
L.append('quit;')
print('\n'.join(L))
