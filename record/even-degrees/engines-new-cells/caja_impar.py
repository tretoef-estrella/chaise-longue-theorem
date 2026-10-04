# caja_impar.py — Grepy Chats, 2 Oct 2026. The odd box over any prime field.
# Usage: python3 -u caja_impar.py k r p [nosign]
#   dim_{F_p} of the ideal (D_J : J) in C_r = F_p[y_1..y_{2k+1}]/(y_i^r), D_J = prod over the k pairs of J not containing 0
#   of D_r(a,b) = sum_u (-1)^u a^u b^{r-1-u}  (with "nosign": sum_u a^u b^{r-1-u}, a negative control in odd characteristic),
#   against N_r(2k+2) = (2k+2)! [t^(2k+2)] cosh(t) I_0(2t)^((r-1)/2), the number of (2k+2)-tuples in a set of r elements
#   with an involution with one fixed point whose multiset is closed under the involution (the fixed value used an even number of times).
import sys, itertools, numpy as np
from fractions import Fraction
from math import factorial
from azotea import matchings, rank_f2, rank_fp

def N(r, n):
    def mul(a, b):
        c = [Fraction(0)]*(n+1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i+j <= n: c[i+j] += x*y
        return c
    cosh = [Fraction(1, factorial(i)) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    I0 = [Fraction(1, factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    s = cosh
    for _ in range((r-1)//2): s = mul(s, I0)
    return int(s[n]*factorial(n))

def run(k, r, p, sign=True):
    n1 = 2*k+1; shape = (r,)*n1
    def sh(A, a, ax):
        if a == 0: return A
        B = np.zeros_like(A); src = [slice(None)]*n1; dst = [slice(None)]*n1
        src[ax] = slice(0, r-a); dst[ax] = slice(a, r); B[tuple(dst)] = A[tuple(src)]; return B
    vecs = []
    for J in matchings(list(range(n1+1))):
        ks = [l for (j, l) in J]
        A = np.zeros(shape, np.int64); A[(0,)*n1] = 1
        for (j, l) in J:
            if j == 0: continue
            S = np.zeros_like(A)
            for u in range(r):
                c = (-1)**u if sign else 1
                S += c*sh(sh(A, u, j-1), r-1-u, l-1)
            A = S % p
        for nu in itertools.product(range(r), repeat=len(ks)):
            B = A
            for l, e in zip(ks, nu): B = sh(B, e, l-1)
            if B.any(): vecs.append(B.reshape(-1).astype(np.uint8))
    if p == 2:
        d = len(rank_f2([int.from_bytes(np.packbits(v).tobytes(), 'big') for v in vecs]))
    else:
        d = rank_fp(np.array(vecs), p)
    target = N(r, 2*k+2)
    print(f"BOX k={k} r={r} p={p} sign={sign}: dim C={r**n1} dim ideal={d} N_r={target} equal: {d == target}", flush=True)

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sign=(len(sys.argv) < 5))
    print("FIN-OK", flush=True)
