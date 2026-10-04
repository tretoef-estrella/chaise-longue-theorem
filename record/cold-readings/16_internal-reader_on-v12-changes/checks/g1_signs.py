# G1 — P1, P2, M2: the signs of §8.3 and Lemma 8.8, against the Pfaffian computed from the definition.
# Every test has a negative control that must FAIL at least once.
import random, itertools, sys
sys.path.insert(0, 'checks')
from pflib import *

rng = random.Random(20261004)
res = {}
def rec(name, ok_count, total, ctrl_fail):
    res[name] = (ok_count, total, ctrl_fail)
    print(f'{name}: {ok_count}/{total} hold; control failed in {ctrl_fail} cases', flush=True)

# T1: sgn(pi) = (-1)^{crossings}
ok = tot = cf = 0
for n in range(0, 11, 2):
    for m in matchings(list(range(n))):
        tot += 1
        sg = perm_sign([v for pr in m for v in pr])
        ok += (sg == (-1)**crossings(m))
        nest = sum(1 for (a,b),(x,y) in itertools.combinations(m,2) if a<x<y<b or x<a<b<y)
        cf += (sg != (-1)**nest)
rec('T1 sgn = (-1)^crossings (all matchings, n<=10)', ok, tot, cf)

# T2 (i)
ok = tot = cf = 0
for n in range(2, 9):
    for _ in range(25):
        A = rand_alt(n, rng=rng); p = list(range(n)); rng.shuffle(p)
        Ap = [[A[p[i]][p[j]] for j in range(n)] for i in range(n)]
        lhs = pf_def(Ap, n); rhs = perm_sign(p) * pf_def(A, n)
        tot += 1; ok += (lhs == rhs); cf += (lhs != pf_def(A, n))
rec('T2 (i) permutation', ok, tot, cf)

# T3 (ii) equal rows, over Z, mod 2, mod 4
def equal_rows_matrix(n, mod, rng):
    A = rand_alt(n, rng=rng)
    x, xp = rng.sample(range(n), 2)
    for z in range(n):
        if z in (x, xp): continue
        v = A[x][z] + mod * rng.randint(-2, 2) if mod else A[x][z]
        A[xp][z] = v; A[z][xp] = -v
    v = mod * rng.randint(-2, 2) if mod else 0
    A[x][xp] = v; A[xp][x] = -v
    return A, x, xp
for mod in (0, 2, 4):
    ok = tot = cf = 0
    for n in range(2, 9):
        for _ in range(30):
            A, x, xp = equal_rows_matrix(n, mod, rng)
            P = pf_def(A, n)
            tot += 1
            ok += (P == 0) if mod == 0 else (P % mod == 0)
            # control: break the equality in one entry by +1 (not a multiple of mod)
            B = [r[:] for r in A]
            zs = [z for z in range(n) if z not in (x, xp)]
            if zs:
                z = rng.choice(zs); B[xp][z] += 1; B[z][xp] -= 1
            else:
                B[x][xp] += 1; B[xp][x] -= 1
            Q = pf_def(B, n)
            cf += (Q != 0) if mod == 0 else (Q % mod != 0)
    rec(f'T3 (ii) equal rows, ring {"Z" if mod==0 else "Z/"+str(mod)}', ok, tot, cf)

# T4 (iii) with eps(x,z) as printed; control: branches exchanged
def eps(px, pz):
    return (-1)**(px+pz+1) if px < pz else (-1)**(px+pz)
def eps_bad(px, pz):
    return (-1)**(px+pz) if px < pz else (-1)**(px+pz+1)
def minor(A, rm):
    keep = [i for i in range(len(A)) if i not in rm]
    return [[A[i][j] for j in keep] for i in keep]
ok = tot = cf = 0
for n in range(2, 10, 2):
    for _ in range(15):
        A = rand_alt(n, rng=rng); P = pf_def(A, n)
        for x in range(n):
            s1 = sum(eps(x, z)*A[x][z]*pf_def(minor(A, {x, z}), n-2) for z in range(n) if z != x)
            s2 = sum(eps_bad(x, z)*A[x][z]*pf_def(minor(A, {x, z}), n-2) for z in range(n) if z != x)
            tot += 1; ok += (s1 == P); cf += (s2 != P)
rec('T4 (iii) expansion with eps(x,z)', ok, tot, cf)

def rcols(n, s):
    return [[rng.randint(-4, 4) for _ in range(n)] for _ in range(s)]
def drop(a, b):
    return minor(a, {b})

# T5 (F1)
ok = tot = cf = 0
for n in range(1, 7):
    for s in range(0, 4):
        if (n+s) % 2: continue
        for _ in range(8):
            a = rand_alt(n, rng=rng); c = rcols(n, s); P = pf_b(a, c)
            if n >= 2:
                i, j = rng.sample(range(n), 2)
                p = list(range(n)); p[i], p[j] = p[j], p[i]
                a2 = [[a[p[u]][p[v]] for v in range(n)] for u in range(n)]
                c2 = [[col[p[u]] for u in range(n)] for col in c]
                Q = pf_b(a2, c2); tot += 1; ok += (Q == -P); cf += (Q != P) if P != 0 else 0
            if s >= 2:
                k, l = rng.sample(range(s), 2)
                c3 = c[:]; c3[k], c3[l] = c3[l], c3[k]
                Q = pf_b(a, c3); tot += 1; ok += (Q == -P); cf += (Q != P) if P != 0 else 0
rec('T5 (F1) transpositions', ok, tot, cf)

# T6 (F2): eta_b = (-1)^{n+s+p_b}; additivity; equal borders vanish
ok = tot = cf = 0
for n in range(1, 8):
    for s in range(1, 4):
        if (n+s) % 2: continue
        for _ in range(8):
            a = rand_alt(n, rng=rng); c = rcols(n, s); P = pf_b(a, c)
            rhs = sum((-1)**(n+s+b) * c[-1][b] * pf_b(drop(a, b), [[col[i] for i in range(n) if i != b] for col in c[:-1]]) for b in range(n))
            bad = sum((-1)**(n+s+b+1) * c[-1][b] * pf_b(drop(a, b), [[col[i] for i in range(n) if i != b] for col in c[:-1]]) for b in range(n))
            tot += 1; ok += (rhs == P); cf += (bad != P)
            # additivity and homogeneity in a border column, and equal columns
            d = [rng.randint(-4, 4) for _ in range(n)]; lam = rng.randint(-3, 3); k = rng.randrange(s)
            c4 = [col[:] for col in c]; c4[k] = [lam*c[k][i] + d[i] for i in range(n)]
            c5 = [col[:] for col in c]; c5[k] = d
            tot += 1; ok += (pf_b(a, c4) == lam*P + pf_b(a, c5))
            if s >= 2:
                c6 = [col[:] for col in c]; c6[1] = c6[0][:]
                tot += 1; ok += (pf_b(a, c6) == 0)
rec('T6 (F2) eta_b, additivity, equal borders', ok, tot, cf)

# T7 (F3)
ok = tot = cf = 0
for s in range(0, 6):
    for _ in range(10):
        a = rand_alt(s, rng=rng); c = rcols(s, s)
        P = pf_b(a, c); dt = det([[c[k][i] for k in range(s)] for i in range(s)])
        tot += 1; ok += (P == (-1)**(s*(s-1)//2) * dt); cf += (P != dt)
        ys = [rng.randint(-6, 6) for _ in range(s)]
        P2 = pf_b(a, [[y**e for y in ys] for e in range(s)])
        tot += 1; ok += (P2 == (-1)**(s*(s-1)//2) * vander(ys))
rec('T7 (F3) n = s', ok, tot, cf)

# T8 (F4): vartheta = (-1)^{p_x+n+s}, border signs (-1)^{p_x+n+k}
ok = tot = cf = 0
for n in range(1, 8):
    for s in range(0, 4):
        if (n+s) % 2: continue
        for _ in range(6):
            a = rand_alt(n, rng=rng); c = rcols(n, s); P = pf_b(a, c)
            for x in range(n):
                ax = drop(a, x); keep = [i for i in range(n) if i != x]
                cx = [[col[i] for i in keep] for col in c]
                axcol = [a[x][b] for b in keep]
                th = (-1)**(x+n+s)
                part2 = sum((-1)**(x+n+k) * c[k-1][x] * pf_b(ax, cx[:k-1]+cx[k:]) for k in range(1, s+1))
                rhs = th * pf_b(ax, cx + [axcol]) + part2
                bad = -th * pf_b(ax, cx + [axcol]) + part2
                tot += 1; ok += (rhs == P); cf += (bad != P)
rec('T8 (F4) vartheta and border signs', ok, tot, cf)

# T9 (F5) for r = 3,5,7, with a_N = D^-(y_i,y_j) at integer y
ok = tot = cf = 0
for r in (3, 5, 7):
    for npr in range(1, 6):
        for _ in range(6):
            ys = [rng.randint(-5, 5) for _ in range(npr)]; yx = rng.randint(-5, 5)
            aN = [[Dm(ys[i], ys[j], r) if i != j else 0 for j in range(npr)] for i in range(npr)]
            E = sorted(rng.sample(range(r), rng.randint(0, min(3, r-1))))
            s1 = len(E) + 1
            if (npr + s1) % 2: continue
            yE = [[y**e for y in ys] for e in E]
            L1 = pf_b(aN, yE + [[Dm(yx, y, r) for y in ys]])
            R1 = -sum((-1)**u * yx**(r-2-u) * pf_b(aN, yE + [[y**u for y in ys]]) for u in range(r-1))
            L2 = pf_b(aN, yE + [[Dp(yx, y, r) for y in ys]])
            R2 = sum((-1)**u * yx**(r-1-u) * pf_b(aN, yE + [[y**u for y in ys]]) for u in range(r))
            tot += 2; ok += (L1 == R1) + (L2 == R2)
            for u in range(r):
                Pu = pf_b(aN, yE + [[y**u for y in ys]])
                if u in E:
                    tot += 1; ok += (Pu == 0)
                else:
                    Eu = sorted(E + [u])
                    good = (-1)**sum(1 for e in E if e > u) * pf_b(aN, [[y**e for y in ys] for e in Eu])
                    badv = (-1)**sum(1 for e in E if e < u) * pf_b(aN, [[y**e for y in ys] for e in Eu])
                    tot += 1; ok += (Pu == good); cf += (Pu != badv)
            L3 = pf_b(aN, yE + [[y**(r-1) for y in ys]]) - yx * L1
            tot += 1; ok += (L2 == L3)
rec('T9 (F5) at r=3,5,7', ok, tot, cf)

# T10 (F6)
ok = tot = cf = 0
for rho in range(1, 7):
    for _ in range(10):
        ys = [rng.randint(-7, 7) for _ in range(rho)]
        for u in range(rho):
            val = sum((-1)**(rho+c) * vander(ys[:c-1]+ys[c:]) * ys[c-1]**u for c in range(1, rho+1))
            bad = sum((-1)**(c) * vander(ys[:c-1]+ys[c:]) * ys[c-1]**u for c in range(1, rho+1))
            target = vander(ys) if u == rho-1 else 0
            tot += 1; ok += (val == target); cf += (bad != target)
rec('T10 (F6)', ok, tot, cf)

# T11 (F7) Laplace with sgn(S)
ok = tot = cf = 0
for n in range(0, 9):
    for s in range(0, 5):
        if (n - s) < 0 or (n - s) % 2: continue
        for _ in range(5):
            a = rand_alt(n, rng=rng); c = rcols(n, s); P = pf_b(a, c)
            tot_r = 0
            for S in itertools.combinations(range(n), s):
                sg = (-1)**(sum(S) - s*(s-1)//2)
                comp = [i for i in range(n) if i not in S]
                tot_r += sg * det([[c[k][i] for k in range(s)] for i in S]) * pf_def([[a[i][j] for j in comp] for i in comp], len(comp))
            lhs = (-1)**(s*(s-1)//2) * tot_r
            tot += 1; ok += (lhs == P); cf += (tot_r != P)
rec('T11 (F7) Laplace with sgn(S)', ok, tot, cf)

# T12 Lemma 8.8(i) border shift; control: wrong sign inside a'
ok = tot = cf = 0
for n in range(1, 8):
    for s in range(1, 4):
        if (n+s) % 2: continue
        for _ in range(8):
            a = rand_alt(n, rng=rng); c = rcols(n, s); P = pf_b(a, c)
            lam = [rng.randint(-4, 4) for _ in range(n)]; k = rng.randrange(s)
            a1 = [[a[i][j] + lam[i]*c[k][j] - lam[j]*c[k][i] for j in range(n)] for i in range(n)]
            a2 = [[a[i][j] - lam[i]*c[k][j] + lam[j]*c[k][i] + 2*(lam[i]*c[k][j] - lam[j]*c[k][i]) * 0 for j in range(n)] for i in range(n)]
            # a genuinely different control: shift by lam_i c_k(j) + lam_j c_k(i) (not alternating-preserving -> make it alternating by hand)
            a3 = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    v = a[i][j] + lam[i]*c[k][j] + lam[j]*c[k][i]; a3[i][j] = v; a3[j][i] = -v
            tot += 1; ok += (pf_b(a1, c) == P); cf += (pf_b(a3, c) != P)
rec('T12 Lemma 8.8(i) border shift', ok, tot, cf)

# T13 Lemma 8.8(ii) rank-two update; control: opposite sign
ok = tot = cf = 0
for n in range(0, 8):
    for s in range(0, 4):
        if (n+s) % 2: continue
        for _ in range(8):
            a = rand_alt(n, rng=rng); c = rcols(n, s)
            E = [rng.randint(-4, 4) for _ in range(n)]; O = [rng.randint(-4, 4) for _ in range(n)]
            aa = [[a[i][j] + E[i]*O[j] - O[i]*E[j] for j in range(n)] for i in range(n)]
            L = pf_b(aa, c); R = pf_b(a, c) - pf_b(a, c + [E, O]); Rbad = pf_b(a, c) + pf_b(a, c + [E, O])
            tot += 1; ok += (L == R); cf += (L != Rbad)
rec('T13 Lemma 8.8(ii) rank-two update', ok, tot, cf)

# T14 the elementary operation (used in the proof of Lemma 8.8), over Z and mod 2
ok = tot = cf = 0
for n in range(2, 9, 2):
    for _ in range(20):
        A = rand_alt(n, rng=rng); x, w = rng.sample(range(n), 2); lam = rng.randint(-3, 3)
        B = [r[:] for r in A]
        for z in range(n): B[w][z] += lam*A[x][z]
        for z in range(n): B[z][w] += lam*B[z][x]
        tot += 1; ok += (pf_def(B, n) == pf_def(A, n)) and B[w][w] == 0
        # control: row operation only (not alternating any more -> use only the upper triangle): changes Pf
        C = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(i+1, n):
                v = A[i][j] + (lam*A[x][j] if i == w else 0); C[i][j] = v; C[j][i] = -v
        cf += (pf_def(C, n) != pf_def(A, n))
rec('T14 elementary operation', ok, tot, cf)

print('\nSUMMARY')
allok = True
for k, (o, t, c) in res.items():
    st = 'OK' if o == t else 'FAIL'
    if o != t: allok = False
    print(f'  {st}  {k}: {o}/{t}; control fired {c}')
print('ALL HOLD:', allok)
