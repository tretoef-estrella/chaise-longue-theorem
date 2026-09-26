# regla264_ds.py — Grepy el Lector, 2026-09-23. R1: the literal DS statement vs A = P.
# DS [1405.4683] Thm 1.1(a): Tors(H_n(X)/L_K(X)) = Tors(R/(psi_J : J in K)), R = Z[t_1..t_{n+1}]/(t_i^m - 1),
#   psi_J = prod_{i=0..d}(t_{k_i}-1) * prod_{i>=1} phi(t_{j_i} t_{k_i}),  phi(u) = 1+u+...+u^{m-1}.
# Over Q: dim R/(psi) = m^{n+1} - |Gamma_K|.  Over F_3 (m = q = 3^v): compute dim directly (literal) and in
#   y-coordinates y = t - t^{-1} (claim: F_3[G] = F_3[y]/(y^q), (t_j t_k - 1) = (y_j + y_k), psi ~ tau_J sigma'_J).
# modes: lit q k [drop]   -> Singular script, literal t-form, prints vdim
#        yco q k [drop]   -> Singular script, y-form
#        gam q k [drop]   -> |Gamma_K| by enumeration (python)
#        ext q k [drop]   -> Singular: A_K, bone B_K in the x-world (N = 2k+2 vars), E_K = intersect I_J
# drop = comma list of matching indices removed from J (subfamily K)
import sys, itertools
def matchings(s):
    s = list(s)
    if not s: yield []; return
    a = s[0]
    for i in range(1, len(s)):
        rest = s[1:i] + s[i+1:]
        for m in matchings(rest): yield [(a, s[i])] + m
def fam(k, drop):
    Js = list(matchings(range(2*k+2)))
    return [J for i, J in enumerate(Js) if i not in drop], len(Js)
def lit(q, k, drop):
    K, _ = fam(k, drop); n1 = 2*k+1
    s = ['ring R=3,(t(1..%d)),dp;' % n1, 'ideal I=' + ','.join('t(%d)^%d-1' % (i, q) for i in range(1, n1+1)) + ';']
    for J in K:
        f = '*'.join('(t(%d)-1)' % b for (a, b) in J)
        for (a, b) in J:
            if a == 0: continue
            u = 't(%d)*t(%d)' % (a, b)
            f += '*(' + '+'.join(['1'] + ['(%s)^%d' % (u, r) for r in range(1, q)]) + ')'
        s.append('I=I+(%s);' % f)
    s += ['I=std(I);', 'print("LIT q=%d k=%d |K|=%d vdim=" + string(vdim(I)));' % (q, k, len(K)), 'quit;']
    return '\n'.join(s)
def yco(q, k, drop):
    K, _ = fam(k, drop); n1 = 2*k+1
    s = ['ring R=3,(y(1..%d)),dp;' % n1, 'ideal I=' + ','.join('y(%d)^%d' % (i, q) for i in range(1, n1+1)) + ';']
    for J in K:
        f = '*'.join('y(%d)' % b for (a, b) in J)
        for (a, b) in J:
            if a == 0: continue
            f += '*(y(%d)+y(%d))^%d' % (a, b, q-1)
        s.append('I=I+(%s);' % f)
    s += ['I=std(I);', 'print("YCO q=%d k=%d |K|=%d vdim=" + string(vdim(I)));' % (q, k, len(K)), 'quit;']
    return '\n'.join(s)
def gam(q, k, drop):
    K, _ = fam(k, drop); n1 = 2*k+1; cnt = 0
    for a in itertools.product(range(1, q), repeat=n1):   # exponents of zeta, nonzero
        a0 = (-sum(a)) % q; full = (a0,) + a
        if any(all((full[x] + full[y]) % q == 0 for (x, y) in J) for J in K): cnt += 1
    return cnt
def ext(q, k, drop):
    K, _ = fam(k, drop); N = 2*k+2
    s = ['option(redSB);', 'LIB "elim.lib";', 'ring R=3,(x(0..%d)),dp;' % (N-1), 'ideal box=' + ','.join('x(%d)^%d' % (i, q) for i in range(N)) + ';']
    s.append('ideal E=1; ideal Bn=1; ideal IJ;')
    for J in K:
        s.append('IJ=' + ','.join('x(%d)+x(%d)' % (a, b) for (a, b) in J) + ';')
        s.append('E=intersect(E,IJ); Bn=intersect(Bn,IJ+box);')
    s += ['ideal A=std(E+box); Bn=std(Bn);', 'print("EXT q=%d k=%d |K|=%d A=" + string(vdim(A)) + " B=" + string(vdim(Bn)));' % (q, k, len(K)), 'quit;']
    return '\n'.join(s)
if __name__ == '__main__':
    mode, q, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    drop = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 and sys.argv[4] else []
    if mode == 'gam':
        g = gam(q, k, drop); K, _ = fam(k, drop)
        print('GAM q=%d k=%d |K|=%d Gamma=%d  q^(2k+1)-Gamma=%d' % (q, k, len(K), g, q**(2*k+1) - g))
    elif mode not in ("pts","pbone","ptsq"): print({'lit': lit, 'yco': yco, 'ext': ext}[mode](q, k, drop))

def pts(q, k, drop):   # P_K over F_3 only (q=3): points of union of sheets in F_3^N
    assert q == 3
    K, _ = fam(k, drop); N = 2*k+2; c = 0
    for x in itertools.product(range(3), repeat=N):
        if any(all((x[a] + x[b]) % 3 == 0 for (a, b) in J) for J in K): c += 1
    return c
if __name__ == '__main__' and sys.argv[1] == 'pts':
    print('PTS', pts(int(sys.argv[2]), int(sys.argv[3]), [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 and sys.argv[4] else []))

def pbone(q, k, drop, r=None):   # punctured bone: dim F3[y1..y_{2k+1}]/ intersect_J (I'_J + (y_i^r)), r = q-1
    K, _ = fam(k, drop); n1 = 2*k+1; r = r or q-1
    s = ['option(redSB);', 'ring R=3,(y(1..%d)),dp;' % n1, 'ideal bx=' + ','.join('y(%d)^%d' % (i, r) for i in range(1, n1+1)) + ';', 'ideal G=1; ideal IJ;']
    for J in K:
        g = ['y(%d)+y(%d)' % (a, b) for (a, b) in J if a != 0]
        s.append('IJ=' + (','.join(g) if g else '0') + '; G=intersect(G,IJ+bx);')
    s += ['G=std(G);', 'print("PBONE q=%d k=%d |K|=%d r=%d vdim=" + string(vdim(G)));' % (q, k, len(K), r), 'quit;']
    return '\n'.join(s)
def ptsq(q, k, drop):   # P_K(q) for q = 3^v via F_3^v coordinates
    import math
    v = round(math.log(q, 3)); K, _ = fam(k, drop); N = 2*k+2
    pts3 = list(itertools.product(range(3), repeat=N))
    onJ = [set(i for i, x in enumerate(pts3) if all((x[a]+x[b]) % 3 == 0 for (a, b) in J)) for J in K]
    # a point of F_q^N = v-tuple of F_3^N points; on L_J iff all v components on L_J
    c = 0
    for tup in itertools.product(range(len(pts3)), repeat=v):
        if any(all(t in S for t in tup) for S in onJ): c += 1
    return c
if __name__ == '__main__' and sys.argv[1] in ('pbone', 'ptsq'):
    q, k = int(sys.argv[2]), int(sys.argv[3]); drop = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 and sys.argv[4] else []
    print(pbone(q, k, drop) if sys.argv[1] == 'pbone' else 'PTSQ q=%d k=%d |K|=%d P=%d' % (q, k, len(fam(k, drop)[0]), ptsq(q, k, drop)))
