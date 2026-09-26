"""GATE G1: literal dimension of the ideal (psi_J : J in J) in F_p[G], k = 1.
No colourings, no change of variables: closure of the F_p[G]-module generated
by the three psi_J under multiplication by t_1, t_2, t_3.
Usage: python3 gate_G1.py m p
"""
import sys, time, resource
import numpy as np
from engine import RREFBasis

m, p = int(sys.argv[1]), int(sys.argv[2])
nv = 3                      # t_1, t_2, t_3 (k = 1)
size = m ** nv
# index of exponent tuple (e1,e2,e3) is e1*m^2 + e2*m + e3
def idx(e):
    return (e[0] * m + e[1]) * m + e[2]

def monomial(e):
    v = np.zeros(size, dtype=np.int64); v[idx([x % m for x in e])] = 1; return v

def mul(f, g):
    """product in F_p[G] of two coefficient vectors (dense, via shifts on the support of g)."""
    out = np.zeros(size, dtype=np.int64)
    for j in np.flatnonzero(g):
        e = [(j // (m*m)) % m, (j // m) % m, j % m]
        out = (out + int(g[j]) * shift(f, e)) % p
    return out

# permutation arrays for multiplication by t_i
perm = []
for i in range(nv):
    src = np.arange(size)
    e = np.stack([(src // (m*m)) % m, (src // m) % m, src % m], axis=1)
    e[:, i] = (e[:, i] + 1) % m
    dst = (e[:, 0] * m + e[:, 1]) * m + e[:, 2]
    perm.append(dst)

def shift(f, e):
    """f * t^e"""
    src = np.arange(size)
    ex = np.stack([(src // (m*m)) % m, (src // m) % m, src % m], axis=1)
    ex = (ex + np.array(e)) % m
    dst = (ex[:, 0] * m + ex[:, 1]) * m + ex[:, 2]
    out = np.zeros(size, dtype=np.int64); out[dst] = f; return out

def t(i):          # variable t_i, i in 1..3
    e = [0, 0, 0]; e[i-1] = 1; return monomial(e)
one = monomial([0, 0, 0])
def phi(u):        # 1 + u + ... + u^{m-1}
    acc = one.copy(); pw = one.copy()
    for _ in range(m - 1):
        pw = mul(pw, u); acc = (acc + pw) % p
    return acc

# matchings of {0,1,2,3}: [[0,k0],[j1,k1]]
matchings = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
gens = []
for (j0, k0), (j1, k1) in matchings:
    psi = mul((t(k0) - one) % p, mul((t(k1) - one) % p, phi(mul(t(j1), t(k1)))))
    gens.append(psi)

t0 = time.time()
basis = RREFBasis(size, p, maxrows=4 * (m - 1) * (m - 2))
queue = []
for g in gens:
    v = basis.reduce(g)
    if basis.insert(v):
        queue.append(basis.B[basis.n - 1].copy())
qi = 0
while qi < len(queue):
    w = queue[qi]; qi += 1
    for i in range(nv):
        v = np.zeros(size, dtype=np.int64); v[perm[i]] = w
        if basis.insert(v):
            queue.append(basis.B[basis.n - 1].copy())
dim = basis.dim()
mem = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20
print(f"G1  m={m} p={p}: dim_F_p (psi_J : J) F_p[G] = {dim}   |Gamma| = 3(m-1)(m-2) = {3*(m-1)*(m-2)}   "
      f"quotient dim = {size - dim}   time {time.time()-t0:.1f}s  maxrss {mem:.0f} MB")
