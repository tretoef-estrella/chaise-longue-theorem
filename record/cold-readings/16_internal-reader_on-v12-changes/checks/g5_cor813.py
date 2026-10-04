# G5 — C1: Corollary 8.13 at (r, N) = (3,4), (3,6), (5,4) over Q, F_2, F_3, F_5, F_7.
#  dim M (M = sum_P D_P C_N), dim (D_J) C_{2k+1}, |Gamma| by enumeration, N_r(N) by formula,
#  annihilation I_P * D_P = 0 in the box (control: x_a - x_b), and dim Q[x]/cap_P (I_P + (x^r)) by Singular.
#  Control: one matching removed from the sum.
# Also: census of zero patterns Pf_{E_l}(B_0) over Q in the box (M6(2)).
import sys, itertools, subprocess, math, os
sys.path.insert(0, 'checks')
from pflib import matchings, pf_def
from boxpoly import *

def N_r(N, r):
    h = (r-1)//2; tot = 0
    for a in itertools.product(range(N//2+1), repeat=h):
        zc = N - 2*sum(a)
        if zc < 0: continue
        tot += math.factorial(N) // (math.factorial(zc) * math.prod(math.factorial(x)**2 for x in a))
    return tot

def gamma_count(N, r):
    h = (r-1)//2; T = range(-h, h+1); c = 0
    for tup in itertools.product(T, repeat=N):
        if all(tup.count(u) == tup.count(-u) for u in range(1, h+1)): c += 1
    return c

def ideal_dim(gens, n, r, p):
    """dimension of the ideal (gens) in F[y]/(y^r) (gens homogeneous), by degree."""
    tot = 0
    degs = set()
    for g in gens:
        if not g.is_zero(): degs |= g.degrees()
    for d in range(0, n*(r-1)+1):
        cols = box_monomials(n, r, d)
        if not cols: continue
        ci = {m: k for k, m in enumerate(cols)}
        rows = []
        for g in gens:
            if g.is_zero(): continue
            gd = next(iter(g.degrees()))
            e = d - gd
            if e < 0: continue
            for m in box_monomials(n, r, e):
                hpol = g * BP({m: 1}, n, r, p)
                if hpol.is_zero(): continue
                v = [0]*len(cols)
                for k, c in hpol.d.items(): v[ci[k]] = c
                rows.append(v)
        if rows:
            tot += (nmod_mat(rows, p).rank() if p else fmpz_mat(rows).rank())
    return tot

def singular_intersection_dim(N, r, char, drop=None):
    Ms = list(matchings(list(range(N))))
    if drop is not None: Ms = [P for i, P in enumerate(Ms) if i != drop]
    lines = [f'ring R = {char},(x(0..{N-1})),dp;', 'option(redSB);']
    box = ','.join(f'x({i})^{r}' for i in range(N))
    for k, P in enumerate(Ms):
        gens = ','.join(f'x({a})+x({b})' for (a, b) in P)
        lines.append(f'ideal I{k} = {gens},{box};')
    lines.append('ideal J = intersect(' + ','.join(f'I{k}' for k in range(len(Ms))) + ');')
    lines.append('J = std(J);'); lines.append('print(vdim(J));'); lines.append('quit;')
    src = '\n'.join(lines)
    out = subprocess.run(['Singular', '-q'], input=src, capture_output=True, text=True, timeout=300).stdout.strip()
    return int(out.split()[-1])

results = []
for (r, N) in [(3, 4), (3, 6), (5, 4)]:
    k = N//2 - 1
    nr = N_r(N, r); gm = gamma_count(N, r)
    print(f'(r,N)=({r},{N}): N_r(N) formula = {nr}, |Gamma| enumerated = {gm}, box dim r^N = {r**N}', flush=True)
    # annihilation check over Z
    ann_ok = ann_bad = True
    for (a, b) in [(0, 1)]:
        n = 2
        f = (y(0, n, r, 0) + y(1, n, r, 0)) * Dplus(0, 1, n, r, 0)
        g = (y(0, n, r, 0) - y(1, n, r, 0)) * Dplus(0, 1, n, r, 0)
        ann_ok = f.is_zero(); ann_bad = g.is_zero()
    print(f'   (x_a+x_b)D(x_a,x_b) = 0 in the box: {ann_ok};  control (x_a-x_b)D = 0: {ann_bad}', flush=True)
    for p in [0, 2, 3, 5, 7]:
        n = N
        MP = list(matchings(list(range(N))))
        gensM = []
        for P in MP:
            g = BP.one(n, r, p)
            for (a, b) in P: g = g * Dplus(a, b, n, r, p)
            gensM.append(g)
        dM = ideal_dim(gensM, n, r, p)
        dM_drop = ideal_dim(gensM[1:], n, r, p)
        # (D_J) in 2k+1 variables y_1..y_{2k+1} (indices 0..2k here): products over matchings of 2k of the 2k+1 indices
        n2 = N - 1
        gensJ = []
        for left in range(n2):
            rest = [i for i in range(n2) if i != left]
            for Q in matchings(rest):
                g = BP.one(n2, r, p)
                for (a, b) in Q: g = g * Dplus(a, b, n2, r, p)
                gensJ.append(g)
        dJ = ideal_dim(gensJ, n2, r, p)
        sing = singular_intersection_dim(N, r, p)
        sing_drop = singular_intersection_dim(N, r, p, drop=0)
        fld = 'Q' if p == 0 else f'F_{p}'
        print(f'   {fld}: dim M = {dM}; dim (D_J)C_(2k+1) = {dJ}; dim Q[x]/cap_P(I_P+(x^r)) [Singular] = {sing};'
              f'  controls: dim M with one P removed = {dM_drop}; colength of cap with one P removed = {sing_drop}', flush=True)
        results.append((r, N, fld, nr, gm, dM, dJ, sing, dM_drop, sing_drop))

print('\nTABLE r N field | N_r |Gamma| | dimM dim(DJ) colength(cap) | dimM(-1P) colength(cap,-1P)')
for row in results: print('  ', row)
allok = all(row[5] == row[3] == row[4] == row[6] == row[7] for row in results)
print('ALL EQUAL TO N_r(N):', allok)

# ---- census of zero patterns over Q (M6(2)) ----
print('\nZERO-PATTERN CENSUS over Q, Pf_{E_l}(B_0) in Q[y]/(y^r), |B_0| = l+1+2t')
mism = 0; tested = 0
for r in (3, 5, 7):
    h = (r-1)//2
    for l in range(0, 4):
        for t in range(0, h+2):
            n = l + 1 + 2*t
            if n > (7 if r == 3 else 6 if r == 5 else 5): continue
            E = (r-1,) if l == 0 else tuple(range(l-1))
            # build bordered matrix with BP entries over Q (p = 0)
            Z = BP.zero(n, r, 0); s = len(E)
            M = [[Z]*(n+s) for _ in range(n+s)]
            for a in range(n):
                for b in range(n):
                    if a != b: M[a][b] = Dminus(a, b, n, r, 0)
            for c in range(s):
                for a in range(n):
                    v = BP.var_pow(a, E[c], n, r, 0); M[a][n+c] = v; M[n+c][a] = -v
            P = pf_def(M, n+s, BP.one(n, r, 0), Z)
            predicted_zero = (l >= 1 and t >= h) or (l == 0 and t > h)
            tested += 1; mism += (P.is_zero() != predicted_zero)
            print(f'   r={r} l={l} t={t} n={n}: zero={P.is_zero()}  (Corollary 8.9 predicts zero: {predicted_zero})', flush=True)
print(f'census: {tested} cases, {mism} where zero-ness differs from "zero iff (l>=1,t>=h) or (l=0,t>h)"')
