# grepy_gamma_vdim.py (auditor, MISION 88): vdim(K^unif_mu(n) + Gamma^(l)_r objects with |B| = |A| + w, r in [rmin, rmax]). Args: mu n q l rmin rmax w out.sing. Needs grepy_mapa.py in the same folder.
# vdim(K^unif_mu(n) + (tower objects)) versus |W_mu(n)|.  kind 'G' : (1,1) floors G_r, r=2..; kind 'Gam3' : l=3 objects Gamma^(3)_r, r=2.
# Gamma^(l)_r(A;B) = x_A^{q-l} * sum over the surviving terms of [t^D] E_P(-t) g~_A(t)  (all coefficients equal, see regla262_auditoria §7b).
# Implemented directly: sum_{p} e_p(P) * sum_{i_a <= q-1, sum = D-p} x^i  over the heavy letters A, with D = r(q-1)+|P|+1-l.
import sys, itertools
sys.path.insert(0, '.')
from grepy_mapa import gen
def mono_sum(A, deg, q):
    terms = []
    def rec(i, left, ex):
        if i == len(A) - 1:
            if 1 <= left <= q - 1: terms.append(ex + [left])
            return
        for e in range(1, min(left, q - 1) + 1): rec(i + 1, left - e, ex + [e])
    rec(0, deg, [])
    return ' + '.join('*'.join('x(%d)^%d' % (a, e) for a, e in zip(A, ex)) for ex in terms) or '0'
def gam(A, B, n, q, l):
    P = [i for i in range(1, n + 1) if i not in A and i not in B]; r = len(A)
    D = r * (q - 1) + len(P) + 1 - l
    parts = []
    for p in range(0, len(P) + 1):
        s = mono_sum(A, D - p, q)
        if s == '0': continue
        parts.append('(%s) * elv(list(%s), %d)' % (s, ', '.join('x(%d)' % i for i in P) or '0', p) if P else '(%s)' % s if p == 0 else None)
    parts = [x for x in parts if x]
    return ' + '.join(parts) if parts else '0'
mu = tuple(int(x) for x in sys.argv[1].split(",")); n = int(sys.argv[2]); q = int(sys.argv[3]); l = int(sys.argv[4]); rmin = int(sys.argv[5]); rmax = int(sys.argv[6]); w = int(sys.argv[7]); out = sys.argv[8]
txt = gen(mu, n, q).split('\n')
k = [i for i, s in enumerate(txt) if s.startswith('ideal SK')][0]
add = []
for r in range(rmin, rmax + 1):
    for A in itertools.combinations(range(1, n + 1), r):
        rest = [i for i in range(1, n + 1) if i not in A]
        for B in itertools.combinations(rest, r + w):
            add.append('K = K, %s;' % gam(list(A), list(B), n, q, l))
txt[k:k] = add
txt[-2] = txt[-2].replace('vdim(K^unif)', 'vdim(K^unif + Gamma^(%d)_{%d..%d}, |B|=|A|+%d)' % (l, rmin, rmax, w))
open(out, 'w').write('\n'.join(txt))
print(len(add), 'tower generators added')
