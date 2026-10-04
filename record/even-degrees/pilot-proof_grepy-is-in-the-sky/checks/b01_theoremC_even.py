# b01_theoremC_even.py — pilot. Gate for B3: the bipartite ideals of the paper (section 7) with an EVEN box q = 2^v in characteristic 2.
#   I^bal_a = ( prod_i (x_i + z_sigma(i))^(q-1) : sigma in S_a )              in F_2[x_1..x_a, z_1..z_a]/(x^q, z^q)
#   I^ph_a  = ( prod_{i != i0} (x_i + z_sigma(i))^(q-1) : i0, sigma )          in F_2[x_1..x_{a+1}, z_1..z_a]/(x^q, z^q)
#   N_bal(a, q) = #{(xi, eta) in Omega^a x Omega^a : equal multisets},  N_ph(a, q) = N_bal(a+1, q)
# Multipliers: all monomials in the x-variables suffice, because (x - z)(x - z)^(q-1) = x^q - z^q = 0, so z acts as x.
# Negative control: a single bijection instead of all of them.
import sys, itertools
from math import factorial
from fractions import Fraction
from eng import Box, prod, ideal_from_generators, egf_coeff

def N_bal(a, q):
    ser = [Fraction(1, factorial(c) ** 2) for c in range(a + 1)]
    acc = [Fraction(1)] + [Fraction(0)] * a
    for _ in range(q):
        new = [Fraction(0)] * (a + 1)
        for i, u in enumerate(acc):
            if u:
                for j in range(a + 1 - i):
                    new[i + j] += u * ser[j]
        acc = new
    return int(acc[a] * factorial(a) ** 2)

def lin_pow(box, i, l, q):
    f = box.poly([(1, {i: 1}), (1, {l: 1})])
    g = box.one()
    for _ in range(q - 1):
        g = box.mul(g, f)
    return g

def run(a, q, kind, single=False):
    nx = a if kind == "bal" else a + 1
    box = Box([q] * (nx + a), 2)
    gens, free = [], []
    xs = list(range(nx)); zs = list(range(nx, nx + a))
    if kind == "bal":
        for sig in itertools.permutations(range(a)):
            gens.append(prod(box, [lin_pow(box, xs[i], zs[sig[i]], q) for i in range(a)])); free.append(xs)
            if single: break
    else:
        for i0 in range(nx):
            rest = [i for i in range(nx) if i != i0]
            for sig in itertools.permutations(range(a)):
                gens.append(prod(box, [lin_pow(box, rest[t], zs[sig[t]], q) for t in range(a)])); free.append(xs)
    S = ideal_from_generators(box, gens, free=free)
    target = N_bal(a, q) if kind == "bal" else N_bal(a + 1, q)
    tag = "CONTROL single bijection" if single else kind
    print(f"{tag} a={a} q={q}: dim ideal={S.dim()}  count={target}  equal={S.dim() == target}", flush=True)

if __name__ == "__main__":
    for (a, q) in [(1, 2), (2, 2), (3, 2), (4, 2), (1, 4), (2, 4), (3, 4), (1, 8), (2, 8)]:
        run(a, q, "bal")
    for (a, q) in [(1, 2), (2, 2), (3, 2), (1, 4), (2, 4), (1, 8)]:
        run(a, q, "ph")
    run(2, 2, "bal", single=True); run(2, 4, "bal", single=True)
