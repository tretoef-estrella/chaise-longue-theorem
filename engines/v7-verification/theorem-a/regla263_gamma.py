# regla263_gamma.py — Grepy el Lector, 2026-09-23, MISION 89 (audit of INFORME_14). OWN CODE, not the Fable's.
# Gamma^{(s)}(A;B)(n) := [t^D] E_P(-t) * prod_{a in A} (1-at)/(1+at),  D = r(q-1)+|P|+1-s, P = [n]\(A u B)
#   (B cancels: E_B(-t) * prod_B (1-bt)^{-1} = 1).  Over F_3, mod box (exponents >= q dropped).
# Casilla K^G_mu(n) = (e_odd) + box + (Gamma^{(s)}(A;B)(n) : w=|B|-|A| >= 0, 1 <= s <= lambda_w(mu)), ALL levels written.
# Modes:
#   vdim  q n mu        -> Singular script printing vdim(std(K)) and |W_mu(n)|
#   rows  q n1 mu       -> Singular script: parent K_mu(n1) in n1 letters (z = last), for every row a and every
#                          generator g of K_child(a)(n1-1): NF(z^a g, std(K + z^{a+1})) == 0 ?  prints failures per row
#   ident q             -> pure-Python exact gates of the moves / descent / new-class / raise certificates (random cells)
import sys, itertools, random
from fractions import Fraction
from math import factorial
P3 = 3
import os
CTRL = os.environ.get('CTRL') == '1'   # negative control: drop the top level at w = 0
def add(d, m, c):
    c %= P3
    if c == 0: return
    v = (d.get(m, 0) + c) % P3
    if v: d[m] = v
    else: d.pop(m, None)
def lam(mu, w): return sum(max(0, x - w) for x in mu)
def Ipoly(d, deg):
    p = [Fraction(0)] * (deg + 1); a = 0
    while 2 * a + d <= deg:
        p[2 * a + d] += Fraction(1, factorial(a) * factorial(a + d)); a += 1
    return p
def pmul(a, b, deg):
    c = [Fraction(0)] * (deg + 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            if i + j > deg: break
            c[i + j] += x * y
    return c
def W(mu, n, q):
    h = (q - 1) // 2
    if len(mu) > h: return 0
    p = [Fraction(1, factorial(i)) for i in range(n + 1)]
    for d in mu: p = pmul(p, Ipoly(d, n), n)
    for _ in range(h - len(mu)): p = pmul(p, Ipoly(0, n), n)
    v = p[n] * factorial(n); assert v.denominator == 1
    return int(v)
def norm(m): return tuple(sorted([x for x in m if x > 0], reverse=True))
def rows(mu, q):  # child of row a, a = 0..q-1 (Bessel derivative dictionary)
    l = len(mu); out = []
    lowidx = range(l) if os.environ.get('ROWORDER') != 'small' else range(l - 1, -1, -1)   # control: smallest first
    for i in lowidx:
        c = list(mu); c[i] -= 1; out.append(norm(c))
    out.append(tuple(mu))
    out += [norm(list(mu) + [1])] * (q - 2 * l - 1)
    for i in range(l):
        c = list(mu); c[l - 1 - i] += 1; out.append(norm(c))
    assert len(out) == q
    return out

def gamma(A, P, D, nv, q, cache={}):
    """[t^D] E_P(-t) prod_A (1-at)/(1+at), mod box, over F_3, as dict monomial->coef."""
    key = (tuple(A), tuple(P), D, nv, q)
    if key in cache: return cache[key]
    out = {}
    if D < 0: cache[key] = out; return out
    ci = [1] + [(2 * (-1) ** i) % 3 for i in range(1, q)]   # (1-u)/(1+u) = 1 + 2 sum (-u)^i
    # A-part: all exponent vectors (i_a) with 0<=i_a<=q-1; P-part: subsets
    r = len(A)
    for p in range(0, min(len(P), D) + 1):
        rest = D - p
        if rest > r * (q - 1): continue
        if r == 0 and rest != 0: continue
        # compositions of rest into r parts in [0,q-1]
        def comps(k, left):
            if k == 1:
                if left <= q - 1: yield (left,)
                return
            for x in range(0, min(left, q - 1) + 1):
                for tail in comps(k - 1, left - x): yield (x,) + tail
        Alist = list(comps(r, rest)) if r > 0 else [()]
        sgnp = (-1) ** p
        for S in itertools.combinations(P, p):
            for ex in Alist:
                m = [0] * nv; c = sgnp
                for i in S: m[i] = 1
                for a, e in zip(A, ex):
                    m[a] = e; c *= ci[e]
                add(out, tuple(m), c)
    cache[key] = out
    return out

def casilla(mu, n, q, nv=None, letters=None):
    """generators (list of dicts) of K^G_mu(n) on the given letters (default 0..n-1) inside nv variables."""
    if nv is None: nv = n
    if letters is None: letters = list(range(n))
    gens = []
    seen = set()
    # e_odd
    for k in range(1, n + 1, 2):
        d = {}
        for S in itertools.combinations(letters, k):
            m = [0] * nv
            for i in S: m[i] = 1
            d[tuple(m)] = 1
        gens.append(d)
    if not mu: return gens
    mu1 = mu[0]
    for assign in itertools.product((0, 1, 2), repeat=n):   # 0 -> P, 1 -> A, 2 -> B
        A = [letters[i] for i in range(n) if assign[i] == 1]
        B = [letters[i] for i in range(n) if assign[i] == 2]
        P = [letters[i] for i in range(n) if assign[i] == 0]
        r = len(A); w = len(B) - r
        if w < 0 or w >= mu1: continue
        L = lam(mu, w)
        if CTRL and w == 0: L -= 1
        key0 = (tuple(A), tuple(P))
        if key0 in seen: continue      # B only matters through P
        seen.add(key0)
        for s in range(1, L + 1):
            D = r * (q - 1) + len(P) + 1 - s
            g = gamma(A, P, D, nv, q)
            if g: gens.append(g)
    return gens

def sing_poly(d, names):
    terms = []
    for m, c in d.items():
        mon = '*'.join('%s^%d' % (names[i], e) if e > 1 else names[i] for i, e in enumerate(m) if e > 0)
        cc = c % 3
        if cc == 0: continue
        if mon == '': terms.append(str(cc))
        else: terms.append(('%d*' % cc if cc != 1 else '') + mon)
    return '+'.join(terms) if terms else '0'

def script_vdim(q, n, mu):
    names = ['x(%d)' % (i + 1) for i in range(n)]
    gens = casilla(mu, n, q)
    s = ['option(redSB);', 'ring R=3,(x(1..%d)),dp;' % n, 'ideal I=' + ','.join('x(%d)^%d' % (i + 1, q) for i in range(n)) + ';']
    for g in gens:
        s.append('I=I+(%s);' % sing_poly(g, names))
    s.append('I=std(I);')
    s.append('print("mu=%s n=%d q=%d vdim=" + string(vdim(I)) + " W=%d ngens=%d");' % (str(mu).replace(' ', ''), n, q, W(mu, n, q), len(gens)))
    s.append('quit;')
    return '\n'.join(s)

def script_rows(q, n1, mu):
    n = n1 - 1
    names = ['x(%d)' % (i + 1) for i in range(n1)]   # z = x(n1)
    zi = n1 - 1
    gp = casilla(mu, n1, q)
    s = ['option(redSB);', 'ring R=3,(x(1..%d)),dp;' % n1, 'ideal K=' + ','.join('x(%d)^%d' % (i + 1, q) for i in range(n1)) + ';']
    for g in gp: s.append('K=K+(%s);' % sing_poly(g, names))
    s.append('K=std(K); int bad; int tot=0; poly f; ideal J;')
    ch = rows(mu, q)
    for a in range(q):
        c = ch[a]
        gc = casilla(c, n, q, nv=n1, letters=list(range(n)))
        box_c = ['x(%d)^%d' % (i + 1, q) for i in range(n)]
        s.append('J=std(K+x(%d)^%d); bad=0;' % (n1, a + 1))
        polys = [sing_poly(g, names) for g in gc] + box_c
        for pstr in polys:
            s.append('f=reduce(x(%d)^%d*(%s),J); if(f!=0){bad=bad+1;}' % (n1, a, pstr))
        s.append('print("row %d child %s ngen %d bad=" + string(bad)); tot=tot+bad;' % (a, str(c).replace(' ', ''), len(polys)))
    s.append('print("PARENT mu=%s n1=%d q=%d TOTAL_BAD=" + string(tot));' % (str(mu).replace(' ', ''), n1, q))
    s.append('quit;')
    return '\n'.join(s)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode in ('vdim', 'rows'):
        q = int(sys.argv[2]); n = int(sys.argv[3])
        mu = tuple(int(x) for x in sys.argv[4].split(',') if x) if len(sys.argv) > 4 and sys.argv[4] != 'e' else ()
        print(script_vdim(q, n, mu) if mode == 'vdim' else script_rows(q, n, mu))
    elif mode == 'W':
        q = int(sys.argv[2]); n = int(sys.argv[3])
        mu = tuple(int(x) for x in sys.argv[4].split(',') if x) if len(sys.argv) > 4 and sys.argv[4] != 'e' else ()
        print(W(mu, n, q))
