# a03_r3.py — pilot. Leg A / R3 with my own linear algebra (not Groebner): m = q = 2^v, p = 2, B = F_2[s]/(s_i^q).
#   true ideal  (psi_J),  psi_J = prod_{i=0..k} s_{k_i} * prod_{i=1..k} (s_j + s_k + s_j s_k)^(q-1)   (not homogeneous)
#   tangent ideal (L_J),  L_J  = prod s_{k_i} * prod (s_j + s_k)^(q-1)                                (homogeneous)
# The Hilbert function of in(true ideal) (lowest-degree forms) is read from an echelon form whose pivots are the monomials
# of lowest degree; that of the tangent ideal from the graded engine. Usage: a03_r3.py k q
import sys, numpy as np
from collections import Counter
from eng import Box, matchings, prod, N_odd, ideal_from_generators, monomials_of_degree

def main(k, q):
    n = 2 * k + 1
    box = Box([q] * n, 2)
    Js = matchings(range(n + 1))
    # whole-box positions, lowest degree first
    size = q ** n
    idx = np.arange(size)
    exps = np.stack([(idx // q ** (n - 1 - i)) % q for i in range(n)], axis=1)
    deg = exps.sum(axis=1)
    order = np.argsort(deg, kind='stable')
    rank = np.empty(size, dtype=np.int64); rank[order] = np.arange(size)
    degsorted = deg[order]
    w = np.array([q ** (n - 1 - i) for i in range(n)], dtype=np.int64)
    def vec(f):
        bits = np.zeros(size, dtype=np.uint8)
        np.bitwise_xor.at(bits, rank[f[0] @ w], 1)
        return int.from_bytes(np.packbits(bits).tobytes(), 'big') >> ((-size) % 8)
    basis = {}
    tang_gens, free = [], []
    for J in Js:
        true = box.one(); tang = box.one()
        ks = []
        for (j, l) in J:
            v = j - 1; u = l - 1
            ks.append(u)
            true = box.mul(true, box.var(u)); tang = box.mul(tang, box.var(u))
            if j != 0:
                tri = box.poly([(1, {v: 1}), (1, {u: 1}), (1, {v: 1, u: 1})])
                lin = box.poly([(1, {v: 1}), (1, {u: 1})])
                for _ in range(q - 1):
                    true = box.mul(true, tri); tang = box.mul(tang, lin)
        tang_gens.append(tang); free.append(ks)
        for e in range(0, (q - 1) * len(ks) + 1):
            for mrow in monomials_of_degree(tuple([q] * len(ks)), e):
                beta = np.zeros(n, dtype=np.int64); beta[ks] = mrow
                h = box.shift(true, beta)
                if len(h[1]):
                    x = vec(h)
                    while x:
                        hb = x.bit_length() - 1
                        b = basis.get(hb)
                        if b is None:
                            basis[hb] = x; break
                        x ^= b
    hf_true = Counter(int(degsorted[size - 1 - hb]) for hb in basis)
    T = ideal_from_generators(box, tang_gens, free=free)
    hf_tang = T.hf()
    G = N_odd(q - 1, 2 * k + 2)
    D = sorted(set(hf_true) | set(hf_tang))
    print(f"R3 k={k} q={q}: |Gamma|={G}  dim true ideal={len(basis)}  dim tangent ideal={T.dim()}  equal={len(basis) == T.dim() == G}", flush=True)
    print(f"   degrees {D[0]}..{D[-1]}", flush=True)
    print("   HF in(true)  :", [hf_true.get(d, 0) for d in D], flush=True)
    print("   HF tangent   :", [hf_tang.get(d, 0) for d in D], flush=True)
    print("   same Hilbert function:", all(hf_true.get(d, 0) == hf_tang.get(d, 0) for d in D), flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
