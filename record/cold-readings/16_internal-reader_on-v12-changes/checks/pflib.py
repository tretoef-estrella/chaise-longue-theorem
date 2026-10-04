# pflib.py — Grepy Lupa's own Pfaffian code, written from the DEFINITION of §8.3 (sum over perfect
# matchings, sign of the permutation that lists the pairs, each pair increasing).  No expansion formula
# of the paper is used to compute a Pfaffian here: the expansions are what is being tested.
import itertools, random
from functools import reduce

def matchings(idx):
    """all perfect matchings of the list idx (as lists of pairs (a,b), a before b in idx order)"""
    if not idx:
        yield []
        return
    if len(idx) % 2:
        return
    a = idx[0]
    for j in range(1, len(idx)):
        b = idx[j]
        rest = idx[1:j] + idx[j+1:]
        for m in matchings(rest):
            yield [(a, b)] + m

def perm_sign(seq):
    """sign of the permutation that takes sorted(seq) to seq (seq distinct, comparable)"""
    s = 1
    seq = list(seq)
    pos = {v: i for i, v in enumerate(sorted(seq))}
    p = [pos[v] for v in seq]
    seen = [False]*len(p)
    for i in range(len(p)):
        if not seen[i]:
            j = i; L = 0
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            if L % 2 == 0:
                s = -s
    return s

def crossings(m):
    c = 0
    for (a, b), (x, y) in itertools.combinations(m, 2):
        if a < x < b < y or x < a < y < b:
            c += 1
    return c

def pf_def(A, n, one=1, zero=0):
    """Pfaffian of the alternating matrix A (list of lists, indices 0..n-1, totally ordered by position)
    from the definition: sum over perfect matchings pi of sgn(pi) * prod_{x<y in pi} A[x][y]."""
    if n % 2:
        return zero
    tot = zero
    for m in matchings(list(range(n))):
        sg = perm_sign([v for pr in m for v in pr])
        term = one
        for (a, b) in m:
            term = term * A[a][b]
        tot = tot + term if sg == 1 else tot - term
    return tot

def bordered(a, cols, zero=0):
    """the bordered matrix of (a; c_1..c_s): indices N (0..n-1) then the borders; entry (i, border k) = c_k(i)"""
    n = len(a); s = len(cols)
    M = [[zero]*(n+s) for _ in range(n+s)]
    for i in range(n):
        for j in range(n):
            M[i][j] = a[i][j]
    for k in range(s):
        for i in range(n):
            M[i][n+k] = cols[k][i]
            M[n+k][i] = -cols[k][i]
    return M

def pf_b(a, cols, one=1, zero=0):
    M = bordered(a, cols, zero)
    return pf_def(M, len(M), one, zero)

def rand_alt(n, lo=-5, hi=5, rng=random):
    A = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            v = rng.randint(lo, hi)
            A[i][j] = v; A[j][i] = -v
    return A

def det(M):
    """integer determinant by Bareiss (exact)"""
    n = len(M)
    if n == 0:
        return 1
    M = [row[:] for row in M]
    sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            sw = None
            for i in range(k+1, n):
                if M[i][k] != 0:
                    sw = i; break
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
        prev = M[k][k]
    return sign*M[n-1][n-1]

def det_generic(M, one=1, zero=0):
    """determinant by Leibniz (generic ring elements), small sizes only"""
    n = len(M)
    tot = zero
    for p in itertools.permutations(range(n)):
        t = one
        for i in range(n):
            t = t * M[i][p[i]]
        tot = tot + t if perm_sign(p) == 1 else tot - t
    return tot

def vander(ys):
    """Delta = prod_{i<j} (y_j - y_i) = det(y_i^j)"""
    r = 1
    for i in range(len(ys)):
        for j in range(i+1, len(ys)):
            r *= (ys[j] - ys[i])
    return r

def Dm(a, b, r):   # D^-(a,b) = sum_{u=0}^{r-2} (-1)^u a^u b^{r-2-u}
    return sum((-1)**u * a**u * b**(r-2-u) for u in range(r-1))

def Dp(a, b, r):   # D(a,b) = sum_{u=0}^{r-1} (-1)^u a^u b^{r-1-u}
    return sum((-1)**u * a**u * b**(r-1-u) for u in range(r))
