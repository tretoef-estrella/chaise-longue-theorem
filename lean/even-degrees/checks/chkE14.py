# chkE14.py — Grepy Mandalay, 3 Oct 2026. Brute force for E14 (q_oddbox_theorem.md), Part K:
# the case lemma `cases_of_FS` in the Lean convention of `OddShapes.optS`, for every interlaced pair
# of the small levels, and the side conditions of the lifts T1-T8 it feeds. Pure combinatorics.
import sys, itertools
sys.path.insert(0, '/Users/rafa/Desktop/ARBOLYAML/corpus4/regla298_sky')
from fria_engine import Sh, interlaced_pairs, downset_pairs_not_interlaced, minus, plus, F_formula

NCHK = 0; NFAIL = 0
def check(name, ok):
    global NCHK, NFAIL
    NCHK += 1
    if not ok:
        NFAIL += 1
        if NFAIL <= 20: print('FAIL', name, flush=True)

def colLen(lam, c): return sum(1 for x in lam if x >= c)
def addOne(mu): return tuple(mu) + (1,)

def optS(h, mu, d, p):          # Lean: OddShapes.optS, p = 1..2h+1, rows 1-based
    l = len(mu)
    if p <= l: return (minus(mu, p - 1), d)
    if p == l + 1: return (mu, 1 - d)
    if p <= 2 * h + 1 - l: return (addOne(mu), d)
    return (plus(mu, 2 * h + 2 - p - 1), d)

def first_row_of_length(mu, j):  # j 1-based
    return j == 1 or mu[j - 2] > mu[j - 1]
def last_row_of_length(mu, j):
    return j == len(mu) or mu[j] < mu[j - 1]

def case_of(L, h, mu, d, Phi):
    """Return the disjunct of cases_of_FS that holds, with its data, or None."""
    l = len(mu)
    low = 2 if d == 1 else 1
    found = []
    # (A) an addition (and, for d = 0, the middle option with cs = 1)
    for j in range(1, l + 2):
        lam = plus(mu, j - 1) if j <= l else addOne(mu)
        cs = (mu[j - 1] + 1) if j <= l else 1
        if (lam, d) in L and cs >= low and all(colLen(lam, c) == colLen(mu, c) + (1 if c == cs else 0) for c in range(1, 2 * h + 4 + sum(mu))) and colLen(mu, cs) + Phi == 2 * h + 1:
            found.append(('A', cs))
    # (M) the middle option of a marked shape
    if d == 1 and (addOne(mu), 1) in L and (mu, 0) in L and l < h and Phi == 2 * h + 1 - l:
        found.append(('M',))
    # (Z) the zero option
    if (mu, 1 - d) in L and Phi == l + 1:
        found.append(('Z',))
    # (R) an ordinary removal
    for j in range(1, l + 1):
        lam = minus(mu, j - 1); c0 = mu[j - 1]
        if (lam, d) in L and c0 >= low and all(colLen(lam, c) + (1 if c == c0 else 0) == colLen(mu, c) for c in range(1, 2 * h + 4 + sum(mu))) and colLen(mu, c0) == Phi:
            found.append(('R', c0))
    # (R1) the removal emptying the first column of a marked shape
    if d == 1 and l >= 1 and mu[l - 1] == 1 and (minus(mu, l - 1), 1) in L and Phi == l:
        found.append(('R1',))
    return found

def predicted(h, mu, d, Phi):
    """The disjunct the paper's case analysis predicts, from Phi alone."""
    l = len(mu)
    if Phi > 2 * h + 1 - l:
        j0 = 2 * h + 2 - Phi
        return ('A', mu[j0 - 1] + 1)
    if Phi > l + 1:
        return ('A', 1) if d == 0 else ('M',)
    if Phi == l + 1:
        return ('Z',)
    rho = Phi
    if d == 0 or mu[rho - 1] >= 2:
        return ('R', mu[rho - 1])
    return ('R1',)

ctrl = {'noninterlaced': 0, 'row1_for_rho': 0, 'mid_needs_D2': 0}
nsig = 0; npairs = 0
for h in (1, 2, 3):
    r = 2 * h + 1
    for m in range(1, 9):
        S = Sh(m, h)
        if len(S) > 18: continue
        pairs = interlaced_pairs(m, h)
        npairs += len(pairs)
        for L in pairs:
            for (mu, d) in Sh(m - 1, h):
                Phi = F_formula(L, mu, d, h, r)
                check(f'FS<=2h+1 h={h} m={m}', Phi <= 2 * h + 1)
                # initial segment (optS_filter_eq_Icc), re-checked in the Lean convention
                ins = [p for p in range(1, 2 * h + 2) if optS(h, mu, d, p) in L]
                check(f'Icc h={h} m={m} {mu,d}', ins == list(range(1, Phi + 1)))
                if Phi == 0: continue
                nsig += 1
                f = case_of(L, h, mu, d, Phi)
                pr = predicted(h, mu, d, Phi)
                check(f'case h={h} m={m} {mu,d} Phi={Phi} pred={pr} found={f}', pr in f)
                l = len(mu)
                # side conditions of the lifts and the slice
                if pr[0] == 'A':
                    check('A colLen<=2h', colLen(mu, pr[1]) <= 2 * h)
                    if pr[1] >= 2 or d == 0:
                        j0 = 2 * h + 2 - Phi
                        if j0 <= l:
                            check('A first row', first_row_of_length(mu, j0))
                elif pr[0] == 'M':
                    check('M l<h', l < h)
                elif pr[0] == 'Z':
                    check('Z l<=h', l <= h)
                    check('Z h>=1', h >= 1)
                elif pr[0] == 'R':
                    check('R 1<=colLen<=2h+1', 1 <= colLen(mu, pr[1]) <= 2 * h + 1)
                    check('R last row', last_row_of_length(mu, Phi))
                elif pr[0] == 'R1':
                    check('R1 1<=l<=h', 1 <= l <= h)
                for i in range(Phi):
                    check('slice', 2 * h + 1 - Phi <= 2 * h - i)
                # controls
                if pr[0] == 'R' and Phi >= 2:
                    if colLen(mu, mu[0]) != Phi: ctrl['row1_for_rho'] += 1
            print(f'h={h} m={m} pairs so far ok', flush=True) if False else None
        print(f'h={h} m={m}: {len(pairs)} interlaced pairs, checks {NCHK}, fails {NFAIL}', flush=True)
    # control: a pair of down-sets that fails (D2) breaks the initial segment somewhere
    for m in range(2, 6):
        if len(Sh(m, h)) > 14: continue
        for L in downset_pairs_not_interlaced(m, h):
            for (mu, d) in Sh(m - 1, h):
                Phi = F_formula(L, mu, d, h, 2 * h + 1)
                ins = [p for p in range(1, 2 * h + 2) if optS(h, mu, d, p) in L]
                if ins != list(range(1, Phi + 1)): ctrl['noninterlaced'] += 1
                if d == 1 and len(mu) < h and (addOne(mu), 1) in L and (mu, 0) not in L: ctrl['mid_needs_D2'] += 1
print('tails with Phi >= 1:', nsig, ' interlaced pairs:', npairs)
print('checks', NCHK, 'failures', NFAIL)
print('controls (each must be > 0):', ctrl)
print('FIN-OK' if NFAIL == 0 and all(v > 0 for v in ctrl.values()) else 'FIN-WITH-PROBLEMS')
