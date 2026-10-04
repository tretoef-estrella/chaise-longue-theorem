# alas.py — Grepy Chats, 2 Oct 2026. The two wings proposed by Rafa, measured.
# Wing 1 (the turn in the air): in characteristic 2 inversion t -> 1/t is not a sign but a unipotent involution iota;
#   iota + 1 squares to zero. On the tangent ring its leading part is E = sum_i s_i^2 d/ds_i  (E(s^a) = a s^(a+1)).
#   Measured: is the ideal stable, and what is the homology ker/im on it?  (prediction sealed: dimension 1)
# Wing 2 (odd before even): the tangent ideal of degree q = 2^v lies in the Theorem-B ideal of the odd number q+1, same box.
# Usage: python3 -u alas.py k q
import sys, itertools, numpy as np
from azotea import matchings, rank_f2, gamma
from caja_impar import N as Nodd
from fractions import Fraction
from math import factorial

def Q(k, qodd):   # (2k+2)! [x^(2k+2)] I_0(2x)^((qodd-1)/2)
    n = 2*k+2
    def mul(a, b):
        c = [Fraction(0)]*(n+1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i+j <= n: c[i+j] += x*y
        return c
    I0 = [Fraction(1, factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    s = [Fraction(1)] + [Fraction(0)]*n
    for _ in range((qodd-1)//2): s = mul(s, I0)
    return int(s[n]*factorial(n))

def main(k, q):
    n1 = 2*k+1; shape = (q,)*n1
    def sh(A, a, ax):
        if a == 0: return A
        B = np.zeros_like(A); src = [slice(None)]*n1; dst = [slice(None)]*n1
        src[ax] = slice(0, q-a); dst[ax] = slice(a, q); B[tuple(dst)] = A[tuple(src)]; return B
    def E(A):
        R = np.zeros_like(A)
        for ax in range(n1):
            M = np.zeros_like(A); sl = [slice(None)]*n1; sl[ax] = slice(1, q, 2); M[tuple(sl)] = A[tuple(sl)]   # odd exponents
            R ^= sh(M, 1, ax)
        return R
    def pk(A): return int.from_bytes(np.packbits(A.reshape(-1)).tobytes(), 'big')
    Js = list(matchings(list(range(n1+1))))
    tang, Etang, thmB = [], [], []
    for J in Js:
        ks = [l for (j, l) in J]
        Dm = np.zeros(shape, np.uint8); Dm[(0,)*n1] = 1
        for (j, l) in J:
            if j == 0: continue
            S = np.zeros_like(Dm)
            for u in range(q): S ^= sh(sh(Dm, u, j-1), q-1-u, l-1)      # (s_j+s_l)^(q-1)
            Dm = S
        L = Dm
        for l in ks: L = sh(L, 1, l-1)
        for nu in itertools.product(range(q), repeat=len(ks)):
            C = L; Dv = Dm
            for l, e in zip(ks, nu): C = sh(C, e, l-1); Dv = sh(Dv, e, l-1)
            if C.any(): tang.append(pk(C)); Etang.append(pk(E(C)))
            if Dv.any(): thmB.append(pk(Dv))
    # sanity of E on the whole box: E^2 = 0 and homology 2^n1
    rng = np.random.default_rng(1); X = rng.integers(0, 2, shape, dtype=np.uint8)
    e2 = int(E(E(X)).any())
    d = len(rank_f2(tang)); rE = len(rank_f2(Etang)); stab = len(rank_f2(tang + Etang)) == d
    dB = len(rank_f2(thmB)); inside = len(rank_f2(thmB + tang)) == dB
    G, _ = gamma(k, q)
    print(f"WINGS k={k} q={q}: |Gamma|={G} N_(q-1)={Nodd(q-1, 2*k+2)}", flush=True)
    print(f"  wing 1: E^2 != 0 on a random element: {e2}; tangent ideal dim={d}; E-stable: {stab}; rank E on it={rE}; homology ker/im = {d - 2*rE}", flush=True)
    print(f"  wing 2: Theorem-B ideal of the odd number {q+1} in the same box: dim={dB}, Q_k({q+1})={Q(k, q+1)}; tangent ideal inside it: {inside}", flush=True)
    # true ideal with the inversion iota, in the group-ring basis
    m = q; vecs, ivecs = [], []
    def iota(A):
        for ax in range(n1): A = np.roll(np.flip(A, axis=ax), 1, axis=ax)
        return A
    for J in Js:
        A = np.zeros((m,)*n1, np.uint8); A[(0,)*n1] = 1
        ks = [l for (j, l) in J]
        for l in ks: A = np.roll(A, 1, axis=l-1) ^ A
        for (j, l) in J:
            if j == 0: continue
            S = np.zeros_like(A)
            for a in range(m): S ^= np.roll(np.roll(A, a, axis=j-1), a, axis=l-1)
            A = S
        for nu in itertools.product(range(m), repeat=len(ks)):
            Bv = A
            for l, e in zip(ks, nu):
                if e: Bv = np.roll(Bv, e, axis=l-1)
            vecs.append(pk(Bv)); ivecs.append(pk(iota(Bv) ^ Bv))
    dt = len(rank_f2(vecs)); ri = len(rank_f2(ivecs)); st = len(rank_f2(vecs + ivecs)) == dt
    print(f"  wing 1, true ideal: dim={dt}; stable under inversion: {st}; rank(iota+1)={ri}; homology = {dt - 2*ri}", flush=True)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2])); print("FIN-OK", flush=True)
