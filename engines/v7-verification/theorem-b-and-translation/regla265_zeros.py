# regla265_zeros.py — Grepy el Lector, 2026-09-23 (MISION 91). Bisel's test, strong form:
# unpunctured bone B_K(q) (box q, grid with 0)  =?  sum over even zero-sets Z of punctured bones b_{K|Z^c}(q-1).
# K|Z^c = {J minus pairs inside Z : J in K, Z union of pairs of J}. Elimination of the smallest point (all I_J contain e_1).
# Point side identity P_K = sum_Z Gamma_{K|Z^c} is exact by construction.
import sys, itertools
def matchings(s):
    s = list(s)
    if not s: yield []; return
    a = s[0]
    for i in range(1, len(s)):
        for m in matchings(s[1:i] + s[i+1:]): yield [(a, s[i])] + m
def restrict(K, Z):
    out = []
    for J in K:
        inZ = [p for p in J if p[0] in Z and p[1] in Z]
        if sum(2 for p in inZ) == len(Z):
            r = tuple(sorted(p for p in J if p not in inZ))
            if r not in out: out.append(r)
    return out
def count(K, pts, q, zero):   # points c in C^pts (C = Z/q, or Z/q minus 0) on some L_J
    vals = range(q) if zero else range(1, q); c = 0
    idx = {p: i for i, p in enumerate(pts)}
    for x in itertools.product(vals, repeat=len(pts)):
        if any(all((x[idx[a]] + x[idx[b]]) % q == 0 for (a, b) in J) for J in K): c += 1
    return c
def sing_dim(K, pts, box, name):  # dim F3[vars]/ intersect_J (I_J + box) after eliminating pts[0]
    if not K: return None
    if len(pts) == 0: return 'ONE'
    p0 = pts[0]; rest = pts[1:]
    if not rest: return 'ONE'
    vn = {p: 'y(%d)' % (i + 1) for i, p in enumerate(rest)}
    s = ['ring R%s=3,(y(1..%d)),dp;' % (name, len(rest)), 'ideal bx=' + ','.join('%s^%d' % (vn[p], box) for p in rest) + ';', 'ideal G=1; ideal IJ;']
    for J in K:
        g = ['%s+%s' % (vn[a], vn[b]) for (a, b) in J if a != p0 and b != p0]
        s.append('IJ=' + (','.join(g) if g else '0') + '; G=intersect(G,IJ+bx);')
    s.append('G=std(G); print("%s " + string(vdim(G)));' % name)
    return '\n'.join(s)
def family(k, drop):
    Js = list(matchings(range(2 * k + 2)))
    return [tuple(J) for i, J in enumerate(Js) if i not in drop]
if __name__ == '__main__':
    q, k = int(sys.argv[1]), int(sys.argv[2]); drop = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 and sys.argv[3] else []
    V = list(range(2 * k + 2)); K = family(k, drop); scr = ['option(redSB);']; meta = []
    scr.append(sing_dim(K, V, q, 'BONE'))
    meta.append(('BONE', count(K, V, q, True)))
    for r in range(0, len(V) + 1, 2):
        for Z in itertools.combinations(V, r):
            Kz = restrict(K, set(Z)); pts = [p for p in V if p not in Z]
            if not Kz: continue
            nm = 'Z' + ''.join(map(str, Z)) if Z else 'Z'
            g = count(Kz, pts, q, False)
            sd = sing_dim(Kz, pts, q - 1, nm)
            if sd == 'ONE': meta.append((nm, g, 1))
            else: scr.append(sd); meta.append((nm, g))
    scr.append('quit;')
    open(sys.argv[4], 'w').write('\n'.join(scr)); open(sys.argv[4] + '.meta', 'w').write(repr(meta))
