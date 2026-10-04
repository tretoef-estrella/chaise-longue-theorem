# c10_blocks_p2.py — pilot. A direct check of the prime 2 for an even degree m = 2 r' (r' odd) in the literal group ring of [DS],
# independent of the colour reduction and of Theorem C:  F_2[t]/(t^m - 1) = prod over the irreducible factors g of t^r' - 1 over F_2
# of F_2[t]/(g^2). Here m = 6: two factors per variable, A = F_2[t]/((t+1)^2) (dimension 2) and B = F_2[t]/((t^2+t+1)^2) (dimension 4).
# The ideal of the literal generators psi_J is computed in each block (a tensor product of factors, one per variable); by the symmetry
# of the family under permutations of t_1..t_{2k+1}, the dimension depends only on the number b of variables of type B.
# Total: sum_b C(2k+1, b) * dim_b, to be compared with |Gamma| = N_{m-1}(2k+2).
# Usage: c10_blocks_p2.py k
import sys, itertools, numpy as np
from math import comb
from eng import matchings, N_odd

def mult_matrix(modpoly):
    """Matrix of multiplication by t on F_2[t]/(modpoly), modpoly given as list of coefficients (low to high), monic."""
    d = len(modpoly) - 1
    M = np.zeros((d, d), dtype=np.uint8)
    for i in range(d - 1): M[i + 1, i] = 1
    for i in range(d): M[i, d - 1] = modpoly[i]
    return M

def main(k):
    m = 6; n = 2 * k + 1
    TA = mult_matrix([1, 0, 1])                   # (t+1)^2 = t^2 + 1
    TB = mult_matrix([1, 0, 1, 0, 1])             # (t^2+t+1)^2 = t^4 + t^2 + 1
    Js = matchings(range(n + 1))
    total = 0
    for b in range(n + 1):
        types = [TB] * b + [TA] * (n - b)          # variables 1..b of type B, the others of type A
        dims = [T.shape[0] for T in types]
        size = int(np.prod(dims))
        def apply(Arr, i):                         # multiply by t_i
            return np.moveaxis(np.tensordot(types[i], Arr, axes=([1], [i])), 0, i) % 2
        basis = {}; nvec = 0
        for J in Js:
            Arr = np.zeros(dims, dtype=np.uint8); Arr[(0,) * n] = 1
            ks = [l - 1 for (j, l) in J]
            for l in ks: Arr = (apply(Arr, l) + Arr) % 2
            for (j, l) in J:
                if j == 0: continue
                S = Arr.copy(); P = Arr
                for a in range(1, m):
                    P = apply(apply(P, j - 1), l - 1); S = (S + P) % 2
                Arr = S
                if not Arr.any(): break
            if not Arr.any(): continue
            # multiples by the monomials in the k+1 variables t_{k_i}
            def rec(Arr, idx):
                nonlocal nvec
                if idx == len(ks):
                    nvec += 1
                    x = int.from_bytes(np.packbits(Arr.reshape(-1)).tobytes(), 'big')
                    while x:
                        hb = x.bit_length() - 1
                        y = basis.get(hb)
                        if y is None: basis[hb] = x; break
                        x ^= y
                    return
                cur = Arr
                for e_ in range(dims[ks[idx]]):
                    rec(cur, idx + 1)
                    cur = apply(cur, ks[idx])
            rec(Arr, 0)
        d = len(basis); total += comb(n, b) * d
        print(f"  block with {b} variables of type B (ring of dimension {size}): dim ideal = {d}   x {comb(n, b)} blocks", flush=True)
    G = N_odd(m - 1, 2 * k + 2)
    print(f"DIRECT k={k} m={m} p=2: sum over the {2 ** n} blocks = {total}   |Gamma| = N_5({2 * k + 2}) = {G}   equal: {total == G}", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]))
