"""Bipartite ideals: I_a (balanced) and I'_a (phantom) over F_p, box q.
Usage: python3 bipartite.py bal a q p   |   python3 bipartite.py ph a q p
Prints graded dims, total, and the counts N(a,q) / N'(a,q) (formula and, when small, brute force).
"""
import sys, time, itertools, resource
from math import factorial, comb
from collections import Counter
from partB_engine import graded_dims, pmul

def gen_bal(a, q, sigma):
    nv = 2 * a
    g = {tuple([0] * nv): 1}
    for i in range(a):
        j = a + sigma[i]
        f = {}
        for s in range(q):
            e = [0] * nv; e[i] = s; e[j] = q - 1 - s
            f[tuple(e)] = comb(q - 1, s) * ((-1) ** (q - 1 - s))
        g = pmul(g, f, box=q)
    return g

def gens_balanced(a, q):
    return [gen_bal(a, q, s) for s in itertools.permutations(range(a))]

def gens_phantom(a, q):
    """x_1..x_{a+1}, z_1..z_a; generators prod_{i != i0} (x_i - z_{sigma(i)})^{q-1}."""
    nv = 2 * a + 1
    out = []
    for i0 in range(a + 1):
        others = [i for i in range(a + 1) if i != i0]
        for perm in itertools.permutations(range(a)):
            g = {tuple([0] * nv): 1}
            for i, zj in zip(others, perm):
                j = a + 1 + zj
                f = {}
                for s in range(q):
                    e = [0] * nv; e[i] = s; e[j] = q - 1 - s
                    f[tuple(e)] = comb(q - 1, s) * ((-1) ** (q - 1 - s))
                g = pmul(g, f, box=q)
            out.append(g)
    return out

def N_bal(a, q):
    tot = 0
    for comp in itertools.product(range(a + 1), repeat=q):
        if sum(comp) != a: continue
        m = factorial(a)
        for c in comp: m //= factorial(c)
        tot += m * m
    return tot

def N_ph_brute(a, q):
    if q ** (2 * a + 1) > 2_000_000: return None
    cnt = 0
    for xi in itertools.product(range(q), repeat=a + 1):
        cx = Counter(xi)
        for eta in itertools.product(range(q), repeat=a):
            ce = Counter((-v) % q for v in eta)
            if all(cx[v] >= ce[v] for v in ce): cnt += 1
    return cnt

if __name__ == "__main__":
    kind, a, q, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    t0 = time.time()
    if kind == "bal":
        gens = gens_balanced(a, q); nv = 2 * a; N = N_bal(a, q); label = f"I_{a}"
    else:
        gens = gens_phantom(a, q); nv = 2 * a + 1; N = N_ph_brute(a, q); label = f"I'_{a}"
        N2 = N_bal(a + 1, q)
    dims, tot = graded_dims(gens, nv, q, p, verbose=('-v' in sys.argv))
    mem = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20
    extra = "" if kind == "bal" else f"  N(a+1,q) = {N2}"
    print(f"{kind} (a,q)=({a},{q}) over F_{p}: dim {label} = {tot}   count = {N}{extra}   "
          f"graded {list(dims.values())} (from degree {min(dims)})   time {time.time()-t0:.1f}s maxrss {mem:.0f} MB   "
          f"{'EQUAL' if tot == (N if N is not None else N2) else 'DIFFERENT'}")
