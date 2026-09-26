# cmrefl.py — Fable, Mission 15. Usage: python3 -u cmrefl.py K Q LMFILE
# Gamma' = {y in (F_q^x)^n : multiset {y_1..y_n, -sum y} closed under negation}, n = 2k+1 (|Gamma'| = Q_k(q)).
# Computes the lex (y_1 > ... > y_n) standard monomials of I(Gamma') by the Cerlienco-Mureddu recursion
# (Std(Z) = U_j {e_1 = j} x Std({z' in pi(Z) : |fibre(z')| > j}), pi forgets y_1), reflects e -> (q-2) - e
# coordinatewise, and compares with the measured deglex leading-monomial set of (D_J)C in LMFILE.
import sys, itertools
k, q, lmf = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
n = 2*k+1
# F_q arithmetic, q = 3^v: elements as tuples mod irreducible poly; small q only
p = 3; v = 0; t = q
while t > 1: t //= 3; v += 1
irr = {1: [1], 2: [1, 0, 1], 3: [1, 0, 2, 1]}[v]   # x^2+1 (F_9), x^3+2x+1 (F_27): coeffs high->low
def add(a, b): return tuple((x+y) % 3 for x, y in zip(a, b))
def neg(a): return tuple((-x) % 3 for x in a)
els = [e for e in itertools.product(range(3), repeat=v)]
zero = (0,)*v; nz = [e for e in els if e != zero]
def closed(ms):
    ms = list(ms)
    while ms:
        a = ms.pop()
        b = neg(a)
        if b in ms: ms.remove(b)
        else: return False
    return True
G = []
for y in itertools.product(nz, repeat=n):
    s = zero
    for a in y: s = add(s, a)
    x0 = neg(s)
    if x0 == zero: continue
    if closed(list(y) + [x0]): G.append(y)
print('|Gamma\'| =', len(G), flush=True)
def std(Z, m):
    if m == 0: return [()] if Z else []
    fib = {}
    for z in Z: fib.setdefault(z[1:], 0); fib[z[1:]] += 1
    out = []; j = 0
    while True:
        Zj = [zp for zp, c in fib.items() if c > j]
        if not Zj: break
        for e in std(Zj, m-1): out.append((j,) + e)
        j += 1
    return out
S = std(G, n)
R = set(tuple(q-2-x for x in e) for e in S)
L = set(tuple(map(int, l.split())) for l in open(lmf))
print('k=%d q=%d |Std|=%d |LM|=%d  refl(Std_lex(Gamma\')) == LM((D)C): %s' % (k, q, len(S), len(L), R == L), flush=True)
