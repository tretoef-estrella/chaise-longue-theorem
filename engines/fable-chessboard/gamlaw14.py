# gamlaw14.py — Fable, MISION 14. Singular writer for the Gamma-casilla
#   K^G_mu(n) := (e_odd(y)) + box + ( Gamma^{(s)}(A;B) : w = |B|-|A| >= 0, 1 <= s <= lam_w(mu) ),  lam_w(mu) = sum_i (mu_i - w)_+.
# r = |A| = 0 : Gamma^{(s)}(0;B) = +-e_{|S|+1-s}(x_S), S = [n]\B (all levels written);
# r >= 1      : only the TOP level s = lam_w(mu) is written (lower levels are multiples: a*Gamma^{(s)} = -Gamma^{(s-1)} mod box, s <= q-1,
#               gated in s1b.log); the closed form (unit dropped) sum_p e_p(P) h°_{D-p}(x_A), D = r(q-1)+|P|+1-s  (gated in s1a.log).
# Modes:
#   vdim MU N Q OUT            : prints vdim(K^G_mu(N)) and the number of generators.
#   rows MU N1 Q OUT           : parent mu in N1 = n+1 letters (z = x(N1)); for EVERY row a = 0..q-1 checks
#                                z^a * g in K^G_mu(N1) + (z^{a+1}) for every generator g of K^G_{child(a)}(n) (dictionary of MISION_14 §2).
import sys, itertools

def lam(mu, w): return sum(max(m - w, 0) for m in mu)

def hdeg_sum(A, deg, q):
    terms = []
    def rec(i, left, ex):
        if i == len(A) - 1:
            if 1 <= left <= q - 1: terms.append(ex + [left])
            return
        for e in range(1, min(left, q - 1) + 1): rec(i + 1, left - e, ex + [e])
    if len(A) and deg >= len(A): rec(0, deg, [])
    return ' + '.join('*'.join('x(%d)^%d' % (a, e) for a, e in zip(A, ex)) for ex in terms)

def lst(V): return 'list(%s)' % ', '.join('x(%d)' % i for i in V) if V else 'list()'

def gamma(A, B, letters, q, s):
    P = [i for i in letters if i not in A and i not in B]; r = len(A)
    D = r * (q - 1) + len(P) + 1 - s
    if r == 0:
        k = D
        if k < 0 or k > len(P): return None
        return 'elv(%s, %d)' % (lst(P), k) if k > 0 else '1'
    parts = []
    for p in range(0, len(P) + 1):
        hs = hdeg_sum(A, D - p, q)
        if not hs: continue
        parts.append('(%s)' % hs if p == 0 else '(%s) * elv(%s, %d)' % (hs, lst(P), p))
    return ' + '.join(parts) if parts else None

def gens(mu, letters, q):
    """generator strings of K^G_mu on the given letters (list of variable indices)."""
    n = len(letters); G = []
    for k in range(1, n + 1, 2): G.append('elv(%s, %d)' % (lst(letters), k))
    for i in letters: G.append('x(%d)^%d' % (i, q))
    wmax = mu[0] - 1 if mu else -1
    # r = 0, w = 0 (A = B = empty): e_{n+1-s}(y), s <= |mu|
    for s in range(1, lam(mu, 0) + 1):
        g = gamma([], [], letters, q, s)
        if g: G.append(g)
    # r = 0, w >= 1: Tanisaki-type
    for w in range(1, wmax + 1):
        for B in itertools.combinations(letters, w):
            for s in range(1, lam(mu, w) + 1):
                g = gamma([], list(B), letters, q, s)
                if g: G.append(g)
    # r >= 1: top level only
    for r in range(1, n // 2 + 1):
        for w in range(0, wmax + 1):
            s = lam(mu, w)
            if s < 1 or 2 * r + w > n: continue
            assert s <= q - 1
            for A in itertools.combinations(letters, r):
                rest = [i for i in letters if i not in A]
                for B in itertools.combinations(rest, r + w):
                    g = gamma(list(A), list(B), letters, q, s)
                    if g: G.append(g)
    return G

HEAD = ['proc elv(list vl, int k) { if (k < 0) {return(0);} if (k == 0) {return(1);} if (k > size(vl)) {return(0);}\n  list u = delete(vl, size(vl)); return(elv(u, k) + vl[size(vl)] * elv(u, k-1)); }']

def norm(m): return tuple(sorted([x for x in m if x > 0], reverse=True))
def rows(mu, q):
    l = len(mu); out = []
    for i in range(l):
        c = list(mu); c[i] -= 1; out.append(('lower', norm(c)))
    out.append(('value-0', mu))
    out += [('new-class', norm(list(mu) + [1]))] * (q - 2 * l - 1)
    for i in range(l):
        c = list(mu); c[l - 1 - i] += 1; out.append(('raise', norm(c)))
    assert len(out) == q
    return out

def S(mu): return '()' if not mu else '(' + ','.join(map(str, mu)) + ')'

if __name__ == '__main__':
    mode = sys.argv[1]; mu = tuple(int(x) for x in sys.argv[2].split(',') if x); N = int(sys.argv[3]); q = int(sys.argv[4]); out = sys.argv[5]
    L = ['ring r = 3, (x(1..%d)), dp; option(redSB); int t0 = timer;' % N] + HEAD
    if mode == 'vdim':
        G = gens(mu, list(range(1, N + 1)), q)
        L.append('ideal K = %s;' % G[0])
        L += ['K = K, %s;' % g for g in G[1:]]
        L.append('ideal SK = std(K); "LAW mu=%s n=%d q=%d gens=%d vdim(K^G) =", vdim(SK), " secs", timer - t0;' % (S(mu), N, q, len(G)))
    if mode == 'rows':
        n = N - 1; z = N
        Gp = gens(mu, list(range(1, N + 1)), q)
        L.append('ideal K = %s;' % Gp[0]); L += ['K = K, %s;' % g for g in Gp[1:]]
        L.append('int bad; int tot; ideal SA; poly g; int j;')
        R = rows(mu, q)
        done = {}
        for a, (typ, c) in enumerate(R):
            Gc = gens(c, list(range(1, n + 1)), q) if (not c or len(c) <= (q - 1) // 2) else ['1']
            L.append('SA = std(K + ideal(x(%d)^%d)); bad = 0; tot = 0;' % (z, a + 1))
            L.append('ideal C = %s;' % ', '.join(Gc))
            L.append('for (j = 1; j <= ncols(C); j++) { g = x(%d)^%d * C[j]; tot++; if (reduce(g, SA) != 0) { bad++; } }' % (z, a))
            L.append('"ROW parent=%s n+1=%d q=%d a=%d type=%s child=%s: generators", tot, " NOT in row:", bad;' % (S(mu), N, q, a, typ, S(c)))
            L.append('kill C;')
        L.append('"secs", timer - t0;')
    L.append('quit;')
    open(out, 'w').write('\n'.join(L))
    print('written', out)
