# lamproof.py — Fable, Mission 15. Independent check (pure partition arithmetic) of the three lemmas of THEOREM D:
#  P2: for a weak-dominance down-set Lam of Par_m, Lam_i = {mu in Par_{m-1}: F(mu) > i} is a down-set;
#  P3: for every mu with F(mu) >= 1, cover(mu) >= F(mu) - 1, where cover = max of
#      r-1 (r = #{j : mu - e_j in Lam} >= 1; needs mu_{r+1} < mu_r and mu - e_r in Lam),
#      q-2-l (if mu u 1 in Lam), q-1-j0 (j0 = first row with mu + e_j in Lam; needs rows < j0 strictly longer);
#  plus the segment structure of the two row sets.  Usage: python3 -u lamproof.py Q MMAX TRIALS SEED
import sys, random
q, MMAX, TR, SEED = map(int, sys.argv[1:5]); h = (q-1)//2; random.seed(SEED)
def parts_upto(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for p in range(min(n, mx), 0, -1):
        for r in parts_upto(n-p, p): yield (p,) + r
def allpar(m): return [l for s in range(m % 2, m+1, 2) for l in parts_upto(s) if len(l) <= h]
def srt(l): return tuple(sorted([x for x in l if x > 0], reverse=True))
def wdom(a, b):
    sa = sb = 0
    for j in range(max(len(a), len(b))):
        sa += a[j] if j < len(a) else 0; sb += b[j] if j < len(b) else 0
        if sa > sb: return False
    return True
bad = {'P2': 0, 'P3': 0, 'seg': 0}; tests = 0
for t in range(TR):
    m = random.randint(1, MMAX); P = allpar(m)
    gens = random.sample(P, random.randint(1, min(4, len(P))))
    Lam = set(l for l in P if any(wdom(l, g) for g in gens))
    F = {}
    for mu in allpar(m-1):
        l = len(mu)
        minus = [srt(mu[:j] + (mu[j]-1,) + mu[j+1:]) in Lam for j in range(l)]
        plus = [srt(mu[:j] + (mu[j]+1,) + mu[j+1:]) in Lam for j in range(l)]
        N = (l < h) and (srt(mu + (1,)) in Lam)
        f = sum(minus) + sum(plus) + (q-1-2*l)*N
        F[mu] = f; tests += 1
        r = sum(minus)
        if minus != [True]*r + [False]*(l-r): bad['seg'] += 1
        rp = sum(plus); j0 = l - rp + 1
        if plus != [False]*(l-rp) + [True]*rp: bad['seg'] += 1
        if r >= 1 and not (r == l or mu[r] < mu[r-1]): bad['seg'] += 1
        if rp >= 1 and j0 >= 2 and not (mu[j0-2] > mu[j0-1]): bad['seg'] += 1
        if f >= 1:
            cover = -1
            if r >= 1: cover = max(cover, r-1)
            if N: cover = max(cover, q-2-l)
            if rp >= 1: cover = max(cover, q-1-j0)
            if cover < f-1: bad['P3'] += 1
    for i in range(q-1):
        Li = [mu for mu in F if F[mu] > i]
        S = set(Li)
        for mu in Li:
            for la in allpar(m-1):
                if wdom(la, mu) and la not in S: bad['P2'] += 1
print('q=%d MMAX=%d trials=%d shapes=%d  failures %s' % (q, MMAX, TR, tests, bad))
