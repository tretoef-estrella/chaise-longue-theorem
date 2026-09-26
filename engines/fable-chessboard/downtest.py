# downtest.py — Fable, Mission 15. For RANDOM down-sets Lambda (weak dominance) of residual shapes on m points:
#   tight(Lambda) = {(s, columns of lam) : lam in Lambda, s = (m-|lam|)/2}.
#   Checks: (1) Z(m; tight) = Z_Lambda := {M : lambda(R(M)) in Lambda};  (2) KEY with the four rules;
#   (3) the fibre sets Lambda_i are again down-sets;  (4) STRONG: tight(Lambda_i) subset Rules_i(tight(Lambda)).
# Usage: python3 -u downtest.py Q MMAX TRIALS SEED
import sys, random
q, MMAX, TR, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
sys.argv = ['x', '1', str(q)]
from peelcore import *
random.seed(SEED)
def parts_upto(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for p in range(min(n, mx), 0, -1):
        for r in parts_upto(n-p, p): yield (p,) + r
def allpar(m): return [l for s in range(m % 2, m+1, 2) for l in parts_upto(s) if len(l) <= h]
def wdom(a, b):
    sa = sb = 0
    for j in range(max(len(a), len(b))):
        sa += a[j] if j < len(a) else 0; sb += b[j] if j < len(b) else 0
        if sa > sb: return False
    return True
def conj(l): return tuple(sum(1 for x in l if x > c) for c in range(l[0])) if l else ()
def tight(m, l): return ((m - sum(l))//2, tuple(c for c in conj(l) if c >= 2))
def lam_of_type(tau):
    # residual partition of a multiset type: per class |a-b| copies of the majority value
    return tuple(sorted([a-b for (a, b) in tau if a != b], reverse=True))
f1 = f2 = f3 = f4 = 0; tests = 0
for trial in range(TR):
    m = random.randint(2, MMAX); P_ = allpar(m)
    gens = random.sample(P_, random.randint(1, min(3, len(P_))))
    Lam = frozenset(l for l in P_ if any(wdom(l, g) for g in gens))
    fam = canon(m, {tight(m, l) for l in Lam})
    ZL = frozenset(t for t in types(m) if lam_of_type(t) in Lam)
    Zf = frozenset(t for t in types(m) if inZ(t, fam))
    if ZL != Zf:
        f1 += 1
        if f1 <= 3: print('Z-mismatch m=%d Lam=%s' % (m, sorted(Lam)))
        continue
    fib = {t: fibre(t, fam) for t in types(m-1)}
    Pall = {}
    for i in range(q-2, -1, -1):
        Pall[i] = canon(m-1, set(children(m, fam, i)) | (set(Pall[i+1]) if i+1 in Pall else set()))
    P1 = allpar(m-1)
    for i in range(q-1):
        A = frozenset(t for t in fib if fib[t] > i)
        if not A: continue
        tests += 1
        if not all(inZ(t, Pall[i]) for t in A):
            f2 += 1
            if f2 <= 3: print('KEY FAIL m=%d Lam=%s i=%d' % (m, sorted(Lam), i))
        Li = frozenset(lam_of_type(t) for t in A)
        if any(fib[t] > i for t in A) and not all((lam_of_type(t) in Li) == (t in A) for t in fib):
            f3 += 1   # fibre not a function of lambda
        if any(wdom(l, mu) and l not in Li for mu in Li for l in P1):
            f3 += 1
            if f3 <= 3: print('NOT DOWN-SET m=%d Lam=%s i=%d' % (m, sorted(Lam), i))
        tl = canon(m-1, {tight(m-1, l) for l in Li})
        miss = [t for t in tl if t not in Pall[i]]
        if miss:
            f4 += 1
            if f4 <= 3: print('STRONG FAIL m=%d Lam=%s i=%d missing tight types %s' % (m, sorted(Lam), i, miss))
print('q=%d trials=%d tests=%d  Z-mismatch=%d KEY-fail=%d downset/λ-fail=%d strong-fail=%d' % (q, TR, tests, f1, f2, f3, f4))
