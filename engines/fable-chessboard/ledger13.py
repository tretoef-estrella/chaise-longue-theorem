# PART D: the full ledger of row k = 4 (T(10) at the empty profile), generated from the row dictionary (§2 of MISION_13).
# Visited cells = closure of (∅,10) under children; non-leaf = f >= 2. One line per (parent, row type, distinct child).
from collections import OrderedDict
def norm(m): return tuple(sorted([x for x in m if x > 0], reverse=True))
def children(mu, n):
    l = len(mu); f = n-sum(mu); out = []
    # LOWER rows 0..l-1 (largest first)
    for i in range(l):
        c = list(mu); c[i] -= 1
        out.append(('lower', 'row %d' % i, norm(c)))
    if f >= 1: out.append(('value-0', 'row %d' % l, mu))
    if f >= 2:
        out.append(('new-class', 'rows %d..q-%d' % (l+1, l+1), norm(list(mu)+[1])))
        for i in range(l):          # smallest first
            c = list(mu); k = l-1-i; c[k] += 1
            out.append(('raise', 'row q-%d' % (l-i), norm(c)))
    # merge rows with the same (type, child)
    m = OrderedDict()
    for t, r, c in out:
        key = (t, c)
        m[key] = ('rows ' + m[key].replace('row ', '').replace('rows ', '') + ', ' + r.replace('row ', '')) if key in m else r
    return [(t, m[(t, c)], c) for (t, c) in m]
vis = set(); st = [((), 10)]
while st:
    mu, n = st.pop()
    if (mu, n) in vis: continue
    vis.add((mu, n))
    if n == 0: continue
    for t, r, c in children(mu, n):
        if sum(c) <= n-1: st.append((c, n-1))
chk = all(sum(mu) <= min(n, 10-n) for mu, n in vis)
nonleaf = sorted([(mu, n) for mu, n in vis if n-sum(mu) >= 2], key=lambda x: (len(x[0]), x[0], x[1]))
leaves = sorted([(mu, n) for mu, n in vis if n-sum(mu) <= 1])
S = lambda mu: '∅' if not mu else '(' + ','.join(map(str, mu)) + ')'
def src(mu, n, t, c):
    l = len(mu); f = n-sum(mu); fc = (n-1)-sum(c); leafc = fc <= 1
    cas = 'unif+F2' if (mu == (1, 1) and n in (7, 8)) else 'unif'
    if mu == ():
        return cas, 'PROVED', 'I^(n) casilla theorems (INFORME_10 §4.1)'
    if l == 1:
        m = mu[0]
        if t == 'lower': return cas, 'PROVED', 'INFORME_10 §3.2'
        if t == 'value-0': return cas, 'PROVED', 'INFORME_10 §3.2'
        if t == 'raise': return cas, 'PROVED', 'INFORME_10 §3.2'
        if t == 'new-class':
            if m == 1 and n in (8, 9):
                return cas, 'PROVED', 'uniform part: INFORME_10 Thm 2.1/§2.3; F2 of the corrected child (1,1)(%d): **Thm T, this report §2.1 (open #%d)**' % (n-1, 3 if n == 8 else 4)
            return cas, 'PROVED', 'INFORME_10 Thm 2.1 + §2.3 (row 2), rows increase'
    hook = (l >= 2 and all(x == 1 for x in mu[1:]) and mu[0] >= 2)
    if t == 'raise' and hook and c[0] > mu[0]: return cas, 'PROVED', 'INFORME_11 Thm E (large raise)'
    if mu == (2, 2) and t in ('value-0', 'new-class'): return cas, 'PROVED', 'leaf child: INFORME_11 R12 (Thm D + Q)'
    if leafc and t == 'raise' and mu != (1, 1): return cas, 'PROVED', 'leaf child: INFORME_11 §4.2, R11 (q-free; one check at q = 9)'
    if mu == (1, 1):
        if t == 'lower':
            parts = ['Q/Tanisaki/family: INFORME_11 Thm C', '#A = 1 layer: φ at z=0 (INFORME_12 §2.3)']
            if n == 5: parts.append('#A = 2: Lemma M (INFORME_12 §4.2) and Thm Z (this report §3.1)')
            if n == 6: parts.append('#A = 2: **Thm Z, this report §3.1 (open #1)**')
            if n in (7, 8): parts.append('#A = 2: F2 at z=0 (INFORME_12 §2.3)')
            if n == 7: parts.append('#A = 3: Lemma M (INFORME_12 §4.2)')
            if n == 8: parts.append('#A = 3: **Thm Z, this report §3.1 (open #2)**')
            if n == 4: parts[1] = 'layer (#A = 1 only): φ at z=0 (INFORME_12 §4.4)'
            return cas, 'PROVED', '; '.join(parts) + '; row 1: rows increase (INFORME_12 §4.4)'
        if t == 'value-0':
            if n == 8: return cas, 'PROVED', 'uniform child: INFORME_11 Thm A; F2(7): Lemma M (INFORME_12 §4.2)'
            return cas, 'PROVED', 'INFORME_11 Thm A'
        if t == 'new-class': return cas, 'PROVED', 'INFORME_11 Thm B (ℓ = 2)'
        if t == 'raise':
            if n in (4, 5): return cas, 'PROVED', 'leaf child: INFORME_11 §4.2'
            if n == 6: return cas, 'PROVED', 'INFORME_11 §3.4 pieces + f = 2 lemma (INFORME_12 Thm B\')'
            if n == 7: return cas, 'PROVED', 'INFORME_11 §3.4 pieces; #A\' = 1: raise identity of F2; #A\' = 2: Lemma M (INFORME_12 §4.2)'
            if n == 8: return cas, 'PROVED', 'INFORME_11 §3.4 pieces; #A\' = 1: raise identity of F2; #A\' = 2, 3: Lemma M (INFORME_12 §4.2)'
    if l == 2 and mu[1] == 1:   # (m,1)
        if t == 'lower': return cas, 'PROVED', 'INFORME_10 §4.1 (rows 0, 1 of (m,1), §3.3.6); INFORME_11 Thm C / Thm E'
        if t == 'value-0': return cas, 'PROVED', 'INFORME_10 §4.1 (row 2 of (m,1)); INFORME_11 Thm E (VZ)'
        if t == 'new-class': return cas, 'PROVED', 'INFORME_11 Thm E (NC)'
        if t == 'raise':
            if c[0] > mu[0]: return cas, 'PROVED', 'INFORME_11 Thm E (large raise)'
            if mu == (2, 1) and n == 7: return cas, 'PROVED', 'Q, box, N_1(6): Lemma M (INFORME_12 §4.2); family φ^(2): **Thm R, this report §3.3 (open #5)**'
    if mu == (2, 2):
        if t == 'lower': return cas, 'PROVED', 'INFORME_11 Thm C (Q, Tanisaki, family) + f = 2 lemma for the layer N_1(5) (INFORME_12 Thm B\')'
    if mu in ((1, 1, 1), (1, 1, 1, 1)):
        if t == 'lower': return cas, 'PROVED', 'INFORME_11 Thm C'
        if t == 'value-0': return cas, 'PROVED', 'INFORME_11 Thm A'
        if t == 'new-class': return cas, 'PROVED', 'INFORME_11 Thm B (ℓ = %d)' % l
        if t == 'raise' and mu == (1, 1, 1) and n == 7: return cas, 'PROVED', 'INFORME_11 §3.4 pieces + f = 2 lemma (INFORME_12 Thm B\')'
    if mu == (2, 1, 1):
        if t == 'lower' and c == (1, 1, 1): return cas, 'PROVED', 'INFORME_11 Thm C'
        if t == 'lower': return cas, 'PROVED', 'INFORME_11 Thm E (lower)'
        if t == 'value-0': return cas, 'PROVED', 'INFORME_11 Thm E (VZ)'
        if t == 'new-class': return cas, 'PROVED', 'INFORME_11 Thm E (NC)'
        if t == 'raise' and c[0] > mu[0]: return cas, 'PROVED', 'INFORME_11 Thm E (large raise)'
    return cas, 'OPEN', 'no source found'
rows = []
for mu, n in nonleaf:
    for t, r, c in children(mu, n):
        cas, st_, so = src(mu, n, t, c)
        rows.append((S(mu), n, t, r, S(c), cas, st_, so))
print('visited cells: %d (all with |μ| <= min(n,10-n): %s); non-leaf parents: %d; leaves: %d' % (len(vis), chk, len(nonleaf), len(leaves)))
print('| # | parent | n | type | rows | child (n−1) | casilla of parent | status | proof source |')
print('|---|---|---|---|---|---|---|---|---|')
for i, rw in enumerate(rows, 1):
    print('| %d | %s | %d | %s | %s | %s | %s | **%s** | %s |' % ((i,)+rw))
print('| %d | every leaf (f ≤ 1): %s | | lower / value-0 / top power | all | | I_λ + box | **PROVED** | INFORME_11 Thm D, §4.1 |' % (len(rows)+1, ', '.join('%s(%d)' % (S(m), n) for m, n in leaves)))
print('LINES %d ; PROVED %d ; OPEN %d' % (len(rows)+1, sum(1 for r in rows if r[6] == 'PROVED')+1, sum(1 for r in rows if r[6] == 'OPEN')))
