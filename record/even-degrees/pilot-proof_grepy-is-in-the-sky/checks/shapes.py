# shapes.py — pilot. The point side of the odd box: a set T of r = 2h+1 values with an involution with ONE fixed point 0.
# Shape of a tuple M: (lambda, eps) where, class by class {u, -u} (u != 0) with multiplicities a, a', lambda collects the |a - a'| > 0,
# and eps is the parity of the number of zeros (zeros pair with zeros). |lambda| + eps = m (mod 2), l(lambda) <= h.
# Options when one value y is added to a tuple of shape (mu, eps):
#   y = -u_j : (mu - e_j, eps)          1 value for each row j
#   y = +u_j : (mu + e_j, eps)          1 value for each row j
#   y in a class absent from the residue: (mu U 1, eps)      2(h - l) values
#   y = 0    : (mu, 1 - eps)            1 value
import itertools
from functools import lru_cache

def norm(mu):
    return tuple(sorted((x for x in mu if x > 0), reverse=True))

def options(shape, h):
    """List of (new shape, number of values)."""
    mu, eps = shape
    out = []
    l = len(mu)
    for j in range(l):
        lo = list(mu); lo[j] -= 1; out.append(((norm(lo), eps), 1))
        hi = list(mu); hi[j] += 1; out.append(((norm(hi), eps), 1))
    if h - l > 0:
        out.append(((norm(mu + (1,)), eps), 2 * (h - l)))
    out.append(((mu, 1 - eps), 1))
    return out

def shape_of(M, r):
    """M: tuple of residues mod r; involution x -> -x."""
    mult = [0] * r
    for x in M: mult[x] += 1
    lam = []
    for u in range(1, (r + 1) // 2):
        d = abs(mult[u] - mult[r - u])
        if d: lam.append(d)
    return (norm(lam), mult[0] % 2)

@lru_cache(maxsize=None)
def counts(m, r):
    """dict shape -> number of tuples of T^m with that shape (dynamic programming on the options)."""
    h = (r - 1) // 2
    if m == 0:
        return {((), 0): 1}
    prev = counts(m - 1, r)
    cur = {}
    for sh, c in prev.items():
        for new, mult in options(sh, h):
            cur[new] = cur.get(new, 0) + c * mult
    return cur

def fibre(Lam, shape, h):
    return sum(mult for new, mult in options(shape, h) if new in Lam)

def layers(Lam, m, r):
    """Lam: set of shapes at level m. Returns [Lam_0, ..., Lam_{r-1}], Lam_i = tail shapes (level m-1) with more than i completions."""
    h = (r - 1) // 2
    F = {sh: fibre(Lam, sh, h) for sh in counts(m - 1, r)}
    return [frozenset(sh for sh, f in F.items() if f > i) for i in range(r)], F

def size(Lam, m, r):
    c = counts(m, r)
    return sum(c[sh] for sh in Lam)

def show(Lam):
    def s(sh):
        mu, eps = sh
        return ("(" + ",".join(map(str, mu)) + ")" if mu else "()") + ("*" if eps else "")
    return "{" + " ".join(s(x) for x in sorted(Lam, key=lambda t: (sum(t[0]) + t[1], t[1], t[0]))) + "}"

if __name__ == "__main__":
    # self-test: the dynamic programming against brute force
    for r in (3, 5, 7):
        for m in range(0, 5):
            bf = {}
            for M in itertools.product(range(r), repeat=m):
                sh = shape_of(M, r); bf[sh] = bf.get(sh, 0) + 1
            assert bf == counts(m, r), (r, m)
    print("shapes self-test OK")
