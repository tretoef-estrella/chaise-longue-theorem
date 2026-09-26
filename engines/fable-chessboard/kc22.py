# child pieces Kc = Q_(2,2)(6) + box + N_1(6): does it contain phi_jl -/+ phi_lj, phi = y_j^(q-2) e_2(y\l) ?
import itertools, sys
q = int(sys.argv[1]); y = list(range(1, 7))
def lst(S): return 'list(%s)' % ', '.join('x(%d)' % i for i in S) if S else 'list()'
L = ['ring rr = 3, (x(1..6)), dp; option(redSB); int t0 = timer;',
     'proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }',
     'ideal Kc = 0;']
for j in y: L.append('Kc = Kc, x(%d)^%d;' % (j, q))
for k in (1, 3, 4, 5, 6): L.append('Kc = Kc, elv(%s, %d);' % (lst(y), k))
for S in itertools.combinations(y, 5):
    for rr_ in (4, 5): L.append('Kc = Kc, elv(%s, %d);' % (lst(S), rr_))
for a in range(0, 6):
    for A in itertools.combinations(y, a):
        rest = [i for i in y if i not in A]
        if a+1 > len(rest): continue
        for B in itertools.combinations(rest, a+1):
            C = [i for i in rest if i not in B]
            L.append('Kc = Kc, %s;' % ('*'.join(['x(%d)^%d' % (i, q-1) for i in A]+['x(%d)' % i for i in C]) or '1'))
pjl = 'x(1)^%d*elv(%s,2)' % (q-2, lst([1, 3, 4, 5, 6])); plj = 'x(2)^%d*elv(%s,2)' % (q-2, lst([2, 3, 4, 5, 6]))
L.append('degBound = %d; ideal S = std(Kc); degBound = 0;' % q)
L.append('"q=%d: phi_jl in Kc:", reduce(%s, S)==0, "; phi_jl - phi_lj:", reduce(%s - %s, S)==0, "; phi_jl + phi_lj:", reduce(%s + %s, S)==0, "; secs", timer-t0;' % (q, pjl, pjl, plj, pjl, plj))
L.append('quit;')
open(sys.argv[2], 'w').write('\n'.join(L))
