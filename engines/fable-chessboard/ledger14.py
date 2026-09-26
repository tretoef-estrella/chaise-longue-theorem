# ledger14.py — Fable, MISION 14, PART D: the ledger of row k (default k = 5: T(12) at the empty profile), with the Gamma-casilla
#   K^G_mu(n) = (e_odd) + box + (Gamma^{(s)}(A;B) : w = |B|-|A| >= 0, 1 <= s <= lam_w(mu)),  lam_w(mu) = sum_i (mu_i - w)_+
# at EVERY cell (leaves included). One line per (parent, row type, distinct child). For each line the FIRST row a of the block is
# checked; for every object class (s, w) of the child the script looks for the mechanism of INFORME_14 §3 whose index inequalities hold:
#   BASE     : e_odd(y), box                                    -> row 0
#   PASCAL   : s + 1 <= lam_w(mu)                               -> row 0      (move M-P at z = 0)
#   DESCENT  : s <= lam_w(mu) and s - a <= lam_{w+1}(mu)        -> row a      (M-P iterated + M-B)
#   ANTI     : w = 0, s = |mu| + 1, a >= l + 1                  -> row l+1    (odd identity + descent at level |mu|)
#   RAISE    : w >= 1, s = lam_w(mu) + 1, q - c_{w-1}(mu) <= a, 2l <= q-1, lower z-terms by DESCENT  (move M-A)
# A class with no mechanism prints OPEN. The dictionary count |W_mu(n)| = sum_rows |W_child(n-1)| is re-checked at every parent.
import sys
from grepy_verif import W
def norm(m): return tuple(sorted([x for x in m if x > 0], reverse=True))
def lam(mu, w): return sum(max(m - w, 0) for m in mu)
def cnt(mu, w): return sum(1 for m in mu if m > w)          # lam_w - lam_{w+1}
def rows(mu, q):
    l = len(mu); out = []
    for i in range(l):
        c = list(mu); c[i] -= 1; out.append(('lower', norm(c)))
    out.append(('value-0', mu))
    out += [('new-class', norm(list(mu) + [1]))] * (q - 2 * l - 1)
    for i in range(l):
        c = list(mu); c[l - 1 - i] += 1; out.append(('raise', norm(c)))
    return out
def classes(c):
    return [(s, w) for w in range(0, (c[0] if c else 0)) for s in range(1, lam(c, w) + 1)]
def mech(mu, a, s, w, q):
    l = len(mu)
    if s + 1 <= lam(mu, w): return 'PASCAL'
    if s <= lam(mu, w) and s - a <= lam(mu, w + 1): return 'DESCENT'
    if w == 0 and s == sum(mu) + 1 and a >= l + 1: return 'ANTI'
    if w >= 1 and s == lam(mu, w) + 1 and 2 * l <= q - 1:
        sp = lam(mu, w - 1); istar = q - cnt(mu, w - 1)
        if istar <= a and s <= sp:
            # every lower z-term z^i Gamma^{(u)}, i < istar, u = sp - q + 1 + i <= lam_w(mu): DESCENT at row i (or level <= 0)
            if all((sp - q + 1 + i) <= 0 or ((sp - q + 1 + i) <= lam(mu, w) and (sp - q + 1) <= lam(mu, w + 1)) for i in range(0, istar)):
                return 'RAISE'
    return None
def S(mu): return '∅' if not mu else '(' + ','.join(map(str, mu)) + ')'
def ledger(K, q):
    top = 2 * K + 2; vis = set(); st = [((), top)]
    while st:
        mu, n = st.pop()
        if (mu, n) in vis: continue
        vis.add((mu, n))
        if n == 0: continue
        for t, c in rows(mu, q):
            if sum(c) <= n - 1: st.append((c, n - 1))
    lines = []; badcount = 0
    for mu, n in sorted(vis, key=lambda x: (-x[1], len(x[0]), x[0])):
        if n == 0: continue
        R = rows(mu, q)
        assert W(mu, n, q) == sum(W(c, n - 1, q) for t, c in R), (mu, n)
        seen = {}
        for a, (t, c) in enumerate(R):
            key = (t, c)
            if key in seen: seen[key][1].append(a); continue
            seen[key] = (a, [a])
        for (t, c), (a0, al) in seen.items():
            used = {}; openc = []
            for (s, w) in classes(c):
                m = mech(mu, a0, s, w, q)
                if m is None: openc.append((s, w))
                else: used.setdefault(m, []).append((s, w))
            emp = sum(c) > n - 1
            status = 'OPEN' if openc else 'PROVED'
            badcount += bool(openc)
            lines.append((S(mu), n, n - sum(mu), t, al, S(c) + (' [W=∅, K=(1)]' if emp else ''), status, used, openc))
    return vis, lines, badcount
def fmt_rows(al, q):
    def r(a): return str(a) if a < q // 2 else 'q-%d' % (q - a)
    return ', '.join(r(a) for a in al) if len(al) <= 3 and all(al[i + 1] == al[i] + 1 for i in range(len(al) - 1)) and (al[0] >= q // 2 or al[-1] < q // 2) else '%s..%s' % (r(al[0]), r(al[-1]))
if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    qs = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [9, 27, 81, 243]
    for q in qs:
        vis, lines, bad = ledger(K, q)
        nonleaf = [(m, n) for m, n in vis if n - sum(m) >= 2 and n > 0]
        print('## q = %d : visited cells %d (non-leaf parents f >= 2: %d); lines %d; PROVED %d; OPEN %d' % (q, len(vis), len(nonleaf), len(lines), len(lines) - bad, bad))
        if q == qs[0] or '--all' in sys.argv:
            print('| # | parent | n | f | type | rows | child (n−1) | status | mechanism: object classes (s,w) of the child |')
            print('|---|---|---|---|---|---|---|---|---|')
            for i, L in enumerate(lines, 1):
                mu, n, f, t, al, c, st, used, openc = L
                u = '; '.join('%s %s' % (m, ' '.join('(%d,%d)' % x for x in v)) for m, v in used.items()) or 'BASE only'
                if openc: u += '; **OPEN** ' + ' '.join('(%d,%d)' % x for x in openc)
                print('| %d | %s | %d | %d | %s | %s | %s | **%s** | BASE; %s |' % (i, mu, n, f, t, fmt_rows(al, q), c, st, u))
