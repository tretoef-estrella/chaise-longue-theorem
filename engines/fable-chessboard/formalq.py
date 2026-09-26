# formalq.py — Fable 12: "formal q" membership.  Ring F_3[x(1..n), A(h) for heavy h, H(pair)] with relations
#   (a+b) H_ab = b A_b - a A_a      (H_ab stands for h_m(-a,b), A_h for h^m, m = q-2 ODD).
# A membership proved here specialises (A_h -> h^m, H_ab -> h_m(-a,b)) to EVERY odd m, i.e. every q = 3^v.
import itertools
from rowM import E
def formal_script(n, parentG, targets, H, trunc, label, row0z=None, K=0):
    H=sorted(H); idx={h:i+1 for i,h in enumerate(H)}; pairs=list(itertools.combinations(H,2)); pidx={p:i+1 for i,p in enumerate(pairs)}
    L=['ring r = 3, (x(1..%d), A(1..%d)%s), dp;'%(n,len(H),', HH(1..%d)'%len(pairs) if pairs else ''),
       'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }']
    def inst(h,b):
        mon=[]
        for i,o in h.items():
            if o+K<0: return None
            mon.append('x(%d)^%d*A(%d)'%(i,o+K,idx[i]))
        return ('*'.join(mon)+'*' if mon else '')+'('+b+')'
    gens=[]
    for h,b in parentG:
        if row0z is not None and row0z in h: continue
        if not set(h)<=set(H): continue
        g=inst(h,b)
        if g is None: continue
        gens.append('subst(%s, x(%d), 0)'%(g,row0z) if row0z is not None else g)
    for (a,b),k in pidx.items():
        gens.append('(x(%d)+x(%d))*HH(%d) - x(%d)*A(%d) + x(%d)*A(%d)'%(a,b,k,b,idx[b],a,idx[a]))
    if trunc is not None:
        if trunc[0]=='fixed': gens.append('x(%d)^%d'%(trunc[1],trunc[2]))
        else: gens.append('x(%d)^%d*A(%d)'%(trunc[0],trunc[1]+K,idx[trunc[0]]))
    L.append('ideal J = %s; int t0 = timer; ideal SJ = std(J);'%(', '.join(gens)))
    L.append('int bad = 0; int tot = 0;')
    for h,b in targets: L.append('tot++; if (reduce(%s, SJ) != 0) { bad++; }'%inst(h,b))
    L.append('"%s  FORMAL(K=%d) heavy=%s : targets outside:", bad, "of", tot, " std s:", timer - t0;'%(label,K,H))
    L.append('quit;')
    return '\n'.join(L)
