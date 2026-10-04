# G3 — M5 / M6: Lemma 8.7' (a), (b) and Lemma 8.7 as memberships over prime fields (and over Q for Remark (3)),
# the bordered Pfaffian computed from the definition.  Non-zero Pfaffians are counted apart.
# Controls: (C-a) the generators of one set S removed; (C-b) Remark (3): border y^e, e != r-1, in case (b).
import sys, itertools, random
sys.path.insert(0, 'checks')
from pflib import matchings, pf_def
from boxpoly import *

rng = random.Random(777)

def bordered_bp(N, cols, n, r, p):
    k = len(N); s = len(cols); Z = BP.zero(n, r, p)
    M = [[Z]*(k+s) for _ in range(k+s)]
    for a in range(k):
        for b in range(k):
            if a != b: M[a][b] = Dminus(N[a], N[b], n, r, p)
    for c in range(s):
        for a in range(k):
            M[a][k+c] = cols[c][a]; M[k+c][a] = -cols[c][a]
    return M
def pf_N(N, exps, n, r, p):
    cols = [[BP.var_pow(i, e, n, r, p) for i in N] for e in exps]
    M = bordered_bp(N, cols, n, r, p)
    return pf_def(M, len(M), BP.one(n, r, p), BP.zero(n, r, p))
def U_gens(N, size_S, n, r, p, skip_S=None):
    gens = []
    for S in itertools.combinations(N, size_S):
        if skip_S is not None and tuple(S) == tuple(skip_S): continue
        rest = [i for i in N if i not in S]
        for Q in matchings(rest):
            g = vandermonde(S, n, r, p)
            for (i, j) in Q: g = g * Dplus(i, j, n, r, p)
            gens.append(g)
    return gens

stats = {}
def bump(key, **kw):
    d = stats.setdefault(key, {'tests': 0, 'member': 0, 'nonzero': 0, 'nonzero_member': 0, 'ctrl_tests': 0, 'ctrl_fail': 0})
    for k, v in kw.items(): d[k] += v

primes = [2, 3, 5, 7, 101]
cells = [(3, 6), (5, 5), (7, 4), (9, 4)]
for p in primes:
    for (r, nmax) in cells:
        for n in range(1, nmax+1):
            N = list(range(n))
            # case (a): n = s + 2(t+1)
            for s in range(0, n-1):
                if (n - s) % 2: continue
                esets = [tuple(range(s))]                       # E_{s+1}: Lemma 8.7 with l = s+1
                pool = list(range(r))
                if s <= len(pool):
                    e2 = tuple(sorted(rng.sample(pool, s)))
                    if e2 not in esets: esets.append(e2)
                for E in esets:
                    f = pf_N(N, E, n, r, p)
                    gens = U_gens(N, s+2, n, r, p)
                    mem, zero = member(f, gens, n, r, p)
                    key = ('a', 'L8.7' if E == tuple(range(s)) else 'any')
                    bump(key, tests=1, member=int(mem), nonzero=int(not zero), nonzero_member=int(mem and not zero))
                    if not zero:
                        S0 = list(itertools.combinations(N, s+2))[0]
                        mem2, _ = member(f, U_gens(N, s+2, n, r, p, skip_S=S0), n, r, p)
                        bump(key, ctrl_tests=1, ctrl_fail=int(not mem2))
            # case (b): n = s + 1 + 2t, last border y^{r-1}
            for s in range(0, n):
                if (n - s) % 2 == 0: continue
                pool = list(range(r-1))
                if s > len(pool): continue
                esets = [tuple(sorted(rng.sample(pool, s)))] if s else [()]
                for E in esets:
                    f = pf_N(N, E + (r-1,), n, r, p)
                    gens = U_gens(N, s+1, n, r, p)
                    mem, zero = member(f, gens, n, r, p)
                    key = ('b', 'L8.7' if s == 0 else 'any')
                    bump(key, tests=1, member=int(mem), nonzero=int(not zero), nonzero_member=int(mem and not zero))
                    if not zero:
                        S0 = list(itertools.combinations(N, s+1))[0]
                        mem2, _ = member(f, U_gens(N, s+1, n, r, p, skip_S=S0), n, r, p)
                        bump(key, ctrl_tests=1, ctrl_fail=int(not mem2))
                    # (C-b) Remark (3)-type control: replace y^{r-1} by y^e, e not in E, e < r-1 (case s = 0 and s = 1)
                    if s <= 1:
                        for e in range(r-1):
                            if e in E: continue
                            g = pf_N(N, E + (e,), n, r, p)
                            memg, zg = member(g, gens, n, r, p)
                            if not zg:
                                bump(('Cb', f'r={r}'), ctrl_tests=1, ctrl_fail=int(not memg))
        print('done p =', p, 'r =', r, flush=True)

print('\nRESULTS (case, kind): tests, members, non-zero Pf, non-zero members, control tests, control failures')
for k, d in stats.items():
    print(k, d)

# Remark (3) exactly as printed: r = 5, n = 3, Pf(N; y^2) not in U_0(N); positive control Pf(N; y^4) in U_0(N)
print('\nREMARK (3): r=5, n=3')
for p in primes + [0]:
    n, r = 3, 5; N = [0, 1, 2]
    gens = U_gens(N, 1, n, r, p)
    f2 = pf_N(N, (2,), n, r, p); f4 = pf_N(N, (4,), n, r, p)
    m2, z2 = member(f2, gens, n, r, p); m4, z4 = member(f4, gens, n, r, p)
    print(f'  field {"Q" if p == 0 else "F_"+str(p)}: Pf(N;y^2) zero={z2} member={m2};   Pf(N;y^4) zero={z4} member={m4}')
