# degen.py — Fable, Mission 15. Usage: python3 -u degen.py K Q
# The DIGIT DEGENERATION. q = 3^v. B = F_3[y_1..y_n]/(y_j^q), n = 2k+1, filtered by the weight
# wt(y^e) = sum_j sum_i e_{j,i} 4^i (e_{j,i} = base-3 digits of e_j); gr B = F_3[z_{j,i}]/(z_{j,i}^3), z_{j,i} = in(y_j^{3^i}).
# For A_J = I'_J + (y_j^{q-1}) (ann_B of psibar_J, §1.4): gr A_J = Z_J := (z_{a,i}+z_{b,i} : pairs of J avoiding 0, all i)
#   + (N_j = prod_i z_{j,i}^2 : all j) + (z^3)   [both quotients have dim (q-1)^{k+1}].
# Computes  bt := dim gr B / (intersection over J of Z_J)  as the rank of the sum of inverse systems Z_J^perp, where
# Z_J^perp = span of prod over factors f of J (pairs (a,b) avoiding 0, and the singleton c) of
#   prod_i (Z_{a,i} - Z_{b,i})^{[e_{f,i}]}  (resp. prod_i Z_{c,i}^{[e_{c,i}]}),  e_f in {0,1,2}^v minus (2,..,2).
# Everything is multigraded by the digit-degree vector (deg in digit-0 vars, ..., deg in digit-(v-1) vars): rank blockwise.
# Since gr(cap A_J) is contained in cap gr(A_J):  bt <= b_k(q-1) <= Q_k(q).  So bt = Q_k(q) PROVES (S) at (k,q).
import sys, itertools, numpy as np
sys.path.insert(0, '.')
from eng15 import matchings, Q, Basis
k, q = int(sys.argv[1]), int(sys.argv[2])
v = 0; t = q
while t > 1: t //= 3; v += 1
assert 3**v == q
n = 2*k+1
E = [e for e in itertools.product(range(3), repeat=v) if e != (2,)*v]
def pairvec(e):   # list of ((s-digits),(t-digits)) with coefficient sign
    out = []
    for st in itertools.product(*[[(s, ei-s) for s in range(ei+1)] for ei in e]):
        sgn = (-1)**sum(tt for (_, tt) in st)
        out.append((tuple(s for (s, _) in st), tuple(tt for (_, tt) in st), sgn))
    return out
PV = {e: pairvec(e) for e in E}
blocks = {}   # digit-degree vector -> {monomial: col}
rows = {}     # digit-degree vector -> list of dict rows
for J in matchings(range(2*k+2)):
    pairs = [(a-1, b-1) for (a, b) in J if a != 0]
    c = [b-1 for (a, b) in J if a == 0][0]
    for es in itertools.product(E, repeat=k+1):
        # es[0] for c, es[1..] for pairs
        terms = {tuple([(0,)*v]*n): 1}
        mono = [list((0,)*v) for _ in range(n)]
        base = [(0,)*v]*n; base[c] = es[0]
        terms = {tuple(base): 1}
        for (a, b), e in zip(pairs, es[1:]):
            new = {}
            for m, co in terms.items():
                for s, tt, sg in PV[e]:
                    mm = list(m); mm[a] = s; mm[b] = tt; mm = tuple(mm)
                    new[mm] = (new.get(mm, 0) + co*sg) % 3
            terms = {m: x for m, x in new.items() if x}
        dv = tuple(sum(es[f][i] for f in range(k+1)) for i in range(v))
        rows.setdefault(dv, []).append(terms)
tot = 0
for dv in sorted(rows):
    R = rows[dv]; cols = {}
    for r in R:
        for m in r:
            if m not in cols: cols[m] = len(cols)
    Bs = Basis(len(cols))
    for i0 in range(0, len(R), 3000):
        X = np.zeros((len(R[i0:i0+3000]), len(cols)), dtype=np.int64)
        for i, r in enumerate(R[i0:i0+3000]):
            for m, x in r.items(): X[i, cols[m]] = x
        Bs.add(X)
    tot += Bs.B.shape[0]
print('DEGEN k=%d q=%d v=%d  bt=%d  Q=%d  %s' % (k, q, v, tot, Q(k, q), 'EQUAL => (S) PROVED AT THIS CELL' if tot == Q(k, q) else 'bt < Q (degeneration loses %d)' % (Q(k, q)-tot)), flush=True)
