# rowM.py — Fable 12: Lemma-M (monotone) checks of row inclusions, over F_3, heavy exponents written as m + offset.
# A generator = (heavy: dict letter->offset, body: Singular string).  Instantiated at m: prod letter^(m+off) * body.
import itertools
def X(S): return 'list(%s)'%(', '.join('x(%d)'%i for i in S)) if S else 'list()'
def E(S,k):
    if k<0 or k>len(S): return '0'
    if k==0: return '1'
    return 'elv(%s,%d)'%(X(S),k)
def Qgens(mu,letters):
    n=len(letters); f=n-sum(mu); lam=list(mu)+[1]*f
    conj=[sum(1 for x in lam if x>=i) for i in range(1,n+1)]
    dk=lambda k: sum(conj[n-k:]) if k>0 else 0
    G=[({},E(letters,j)) for j in range(1,n+1) if j%2==1 or j>=f+1]
    for k in range(1,n):
        th=max(1,k-dk(k)+1)
        for Ss in itertools.combinations(letters,k):
            for r in range(th,k+1): G.append(({},E(list(Ss),r)))
    return G
def box(letters): return [({i:2},'1') for i in letters]          # y^q = y^(m+2)  (m = q-2)
def layer(w,letters):       # x_A^(q-1) x_C, |B|-|A| <= w, |B|>=1, minimal |B| = |A|+w (and |A| >= 0)
    G=[]; n=len(letters)
    for a in range(0,n+1):
        b=a+w
        if b<1 or a+b>n: continue
        for A in itertools.combinations(letters,a):
            rest=[i for i in letters if i not in A]
            for B in itertools.combinations(rest,b):
                C=[i for i in rest if i not in B]
                G.append(({i:1 for i in A},'*'.join('x(%d)'%i for i in C) or '1'))
    return G
def family(ell,f,letters):  # phi_jl = y_j^(q-ell) sum_{i<ell} y_j^i e_{f+ell-2-i}(y minus {j,l}); q-ell = m+2-ell
    G=[]
    for j in letters:
        for l in letters:
            if j==l: continue
            P=[i for i in letters if i not in (j,l)]
            G.append(({j:2-ell},'('+'+'.join('x(%d)^%d*%s'%(j,i,E(P,f+ell-2-i)) for i in range(ell))+')'))
    return G
def F2fam(f,letters):       # (y_a y_b)^(q-2) e_{f-1}(y minus {c,d})
    G=[]
    for a,b in itertools.combinations(letters,2):
        rest=[i for i in letters if i not in (a,b)]
        for c,d in itertools.combinations(rest,2):
            G.append(({a:0,b:0},E([i for i in letters if i not in (c,d)],f-1)))
    return G
def casilla(mu,letters,withF2=False):
    n=len(letters); ell=len(mu); f=n-sum(mu)
    G=Qgens(mu,letters)+box(letters)+family(ell,f,letters)
    if mu[0]>=2 or ell==1: G+=layer(mu[0]-1,letters)
    if withF2: G+=F2fam(f,letters)
    return G
def subst0(G,z):            # z = 0 in generators (body strings evaluated in Singular with subst)
    out=[]
    for h,b in G:
        if z in h and h[z]+0>=-1: continue   # heavy in z: vanishes at z = 0 (exponent m+off >= 1)
        out.append((h,'subst(%s, x(%d), 0)'%(b,z)))
    return out
def inst(h,b,m):
    mon='*'.join('x(%d)^%d'%(i,m+o) for i,o in h.items())
    return (mon+'*' if mon else '')+'('+b+')'
def script(nvars, parentG, targets, H, trunc, m, label, row0z=None):
    """targets: list of (heavy dict, body); H: heavy set; trunc: None or (z, offset) meaning z^(m+off) or ('fixed', z, k)."""
    L=['ring r = 3, (x(1..%d)), dp;'%nvars,
       'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }']
    if row0z is None:
        gens=[inst(h,b,m) for h,b in parentG if set(h)<=set(H)]
    else:   # row 0 = substitution z = 0; generators heavy in z (exponent >= 1) vanish
        gens=['subst(%s, x(%d), 0)'%(inst(h,b,m),row0z) for h,b in parentG if row0z not in h and set(h)<=set(H)]
    if trunc is not None:
        if trunc[0]=='fixed': gens.append('x(%d)^%d'%(trunc[1],trunc[2]))
        else: gens.append('x(%d)^%d'%(trunc[0],m+trunc[1]))
    L.append('ideal J = %s; J = simplify(J, 2); int t0 = timer; ideal SJ = std(J);'%(', '.join(gens)))
    L.append('int bad = 0; int tot = 0;')
    for h,b in targets: L.append('tot++; if (reduce(%s, SJ) != 0) { bad++; }'%inst(h,b,m))
    L.append('"%s  m=%d  heavy=%s : targets outside J(m):", bad, "of", tot, " (std %%d s)", timer - t0;'%(label,m,sorted(H)))
    L.append('quit;')
    return '\n'.join(L)
def tower(r,letters):       # G_r(A;B) = x_A^(q-2) e_{n-r-1}(y minus B), |A| = |B| = r
    G=[]; n=len(letters)
    for A in itertools.combinations(letters,r):
        rest=[i for i in letters if i not in A]
        for B in itertools.combinations(rest,r):
            G.append(({i:0 for i in A},E([i for i in letters if i not in B],n-r-1)))
    return G
def cas11(letters,rs):      # corrected (1,1) casilla: K^unif + G_r for r in rs
    G=casilla((1,1),letters,False)
    for r in rs:
        if 2*r<=len(letters): G+=tower(r,letters)
    return G
