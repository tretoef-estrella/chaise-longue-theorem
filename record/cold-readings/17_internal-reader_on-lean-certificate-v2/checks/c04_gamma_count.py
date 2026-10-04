# c04: |Gamma_J| computed INDEPENDENTLY of the paper's formula (mandate M2).
#  (1) direct count of the set Gamma of [DS, Definition 1.3]: a = (a_1..a_{n+1}) in mu_m^{n+1},
#      a_i != 1 for all i, and some J = [[j0,k0],...,[jd,kd]] with a_{j_i} a_{k_i} = 1 for i = 1..d.
#      mu_m is represented by exponents mod m (a = zeta^e): a != 1 <=> e != 0; a b = 1 <=> e+e' = 0 mod m.
#  (2) [DS, Remark 4.4]: |Gamma| = constant term of (x_1+..+x_{h-1}+1+x_{h-1}^-1+..+x_1^-1)^{n+2} (m = 2h)
#      or (x_1+..+x_h+x_h^-1+..+x_1^-1)^{n+2} (m = 2h+1)   [Laurent polynomial computed by convolution]
#  (3) the DS polynomials for n = 2, 4, 6 (Remark 4.4; they give |Gamma|, cf. paper footnote 1).
#  (4) a Python transcription of the LEAN definitions QkEven / Qk / Qall (same sums, same nat division).
import itertools, math, sys
from functools import lru_cache

def matchings(points):
    """all perfect matchings of a sorted list, as lists of pairs (j<k) with j the smallest remaining."""
    if not points: yield []; return
    a = points[0]
    for i in range(1, len(points)):
        b = points[i]
        rest = points[1:i] + points[i+1:]
        for M in matchings(rest):
            yield [(a, b)] + M

def gamma_direct(m, k):
    n1 = 2*k + 1
    Js = list(matchings(list(range(2*k + 2))))
    assert len(Js) == math.prod(range(1, 2*k+2, 2))      # (2k+1)!!
    # pairs not containing 0 (i = 1..d); indices refer to a_1..a_{n+1} (a_0 never enters)
    Jp = [[(j, kk) for (j, kk) in J if j != 0] for J in Js]
    cnt = 0
    for e in itertools.product(range(1, m), repeat=n1):  # a_i != 1  <=>  e_i != 0
        a = (None,) + e
        for J in Jp:
            if all((a[j] + a[kk]) % m == 0 for (j, kk) in J):
                cnt += 1; break
    return cnt

def ct_remark44(m, k):
    N = 2*k + 2
    if m % 2 == 0:
        h = m // 2; exps = [0] + [s*i for i in range(1, h) for s in (1, -1)]
        nvar = h - 1
    else:
        h = (m - 1) // 2; exps = [s*i for i in range(1, h+1) for s in (1, -1)]
        nvar = h
    # monomials: x_i^{+-1} as unit vectors in Z^nvar; '1' as zero vector
    terms = []
    if m % 2 == 0: terms.append((0,)*nvar)
    for i in range(nvar):
        for s in (1, -1):
            v = [0]*nvar; v[i] = s; terms.append(tuple(v))
    poly = {(0,)*nvar: 1}
    for _ in range(N):
        new = {}
        for mono, c in poly.items():
            for t in terms:
                mm = tuple(x+y for x, y in zip(mono, t))
                new[mm] = new.get(mm, 0) + c
        poly = new
    return poly.get((0,)*nvar, 0)

def ds_poly(m, k):
    d = 1 if m % 2 == 0 else 0   # delta_m = m-1 mod 2
    if k == 1: return 3*m*m - 9*m + 6 + d
    if k == 2: return 15*m**3 - 90*m*m + 175*m - 100 + (15*m - 39)*d
    if k == 3: return 105*m**4 - 1050*m**3 + 3955*m*m - 6335*m + 3325 + (210*m*m - 1302*m + 2010)*d
    return None

def piFinset(h, bound):
    return itertools.product(range(bound), repeat=h)

def QkEven(k, m):   # transcription of EvenCount.QkEven (Lean nat subtraction/division)
    h = max(m - 2, 0) // 2; tot = 0
    for c in range(k + 2):
        for b in piFinset(h, 2*k + 3):
            if 2*c + 2*sum(b) == 2*k + 2:
                tot += math.factorial(2*k + 2) // (math.factorial(2*c) * math.prod(math.factorial(x)**2 for x in b))
    return tot

def Qk(k, q):       # transcription of TheoremB.Qk
    h = max(q - 1, 0) // 2; tot = 0
    for b in piFinset(h, 2*k + 3):
        if 2*sum(b) == 2*k + 2:
            tot += math.factorial(2*k + 2) // math.prod(math.factorial(x)**2 for x in b)
    return tot

def Qall(m, k): return QkEven(k, m) if m % 2 == 0 else Qk(k, m)

from fractions import Fraction
def gf_even(k, m):  # N! [x^N] cosh(x) I0(2x)^((m-2)/2), exact series arithmetic (paper's formula; used only for the §9.1 table)
    N = 2*k + 2; h = (m - 2)//2
    cosh = [Fraction(1, math.factorial(i)) if i % 2 == 0 else Fraction(0) for i in range(N+1)]
    I0 = [Fraction(1, math.factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(N+1)]
    def mul(a, b): return [sum(a[i]*b[j-i] for i in range(j+1)) for j in range(N+1)]
    s = cosh
    for _ in range(h): s = mul(s, I0)
    v = s[N]*math.factorial(N); assert v.denominator == 1; return int(v)

cells = [(3,1),(4,1),(5,1),(6,1),(4,2),(7,1),(8,1),(9,1)]
extra = [(m, 0) for m in range(1, 10)] + [(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(5,2),(6,2),(3,3),(4,3),(10,1),(12,1),(11,1)]
bad = 0
print(' m  k | direct Gamma | Remark4.4 CT | DS poly | Lean-transcribed Qall | m^(2k+1) | agree')
for (m, k) in cells + extra:
    g = gamma_direct(m, k)
    ct = ct_remark44(m, k) if m >= 2 else None
    dp = ds_poly(m, k) if m >= 3 else None
    q = Qall(m, k)
    ok = (g == q) and (ct is None or ct == g) and (dp is None or dp == g)
    bad += (not ok)
    print(f'{m:2d} {k:2d} | {g:12d} | {str(ct):>12} | {str(dp):>7} | {q:21d} | {m**(2*k+1):8d} | {ok}')
print('disagreements:', bad)
# paper §9.1 table (even m) and §3 small cases are compared by the Lean-transcribed formula only (cheap):
paper91 = {4: [19,141,1107,8953,73789], 6: [61,1001,18733,375745,7858225], 8: [127,3301,103279,3595177,133789789],
           10: [217,7761,345465,17605249,980612161], 12: [331,15101,876331,59415961,4481629021], 16: [631,41301,3529863,361612105,42214788925]}
b2 = 0
for m, row in paper91.items():
    for k, v in enumerate(row, 1):
        c = ct_remark44(m, k) if (m <= 8 and k <= 3) else gf_even(k, m)
        if c != v: b2 += 1; print('  paper §9.1 table mismatch', m, k, v, c)
print('paper §9.1 table: cells', sum(len(r) for r in paper91.values()), 'mismatches', b2)
# Q_1(m) closed forms: even 3m^2-9m+7, odd 3(m-1)(m-2)
print('closed forms k=1 for m=3..16:', all(Qall(m,1) == (3*m*m-9*m+7 if m%2==0 else 3*(m-1)*(m-2)) for m in range(3, 17)))
# Q_k(m) <= (m-1)^(2k+1) < m^(2k+1): never truncated (and the rank m^(2k+1)-Q is >= 1)
print('Q <= (m-1)^(2k+1) for m=1..12, k=0..3:', all(Qall(m,k) <= (m-1)**(2*k+1) for m in range(1,13) for k in range(0,4)))
