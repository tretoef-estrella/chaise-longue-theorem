# alas_lapiz_check.py — Grepy Chats, 2 Oct 2026. Two pencil identities of §3 bis, checked exactly.
from math import comb, factorial
from fractions import Fraction
from caja_impar import N as Nodd
ok = True
for r in (3, 5, 7, 9, 11, 15):
    D = {(u, r-1-u): 1 for u in range(r)}                       # D_r over F_2
    ED = {}
    for (i, j), c in D.items():
        if i % 2: ED[(i+1, j)] = ED.get((i+1, j), 0) ^ 1          # E(a^i b^j) = i a^(i+1) b^j + j a^i b^(j+1)
        if j % 2: ED[(i, j+1)] = ED.get((i, j+1), 0) ^ 1
    ED = {m for m, c in ED.items() if c}
    target = {(u+1, r-2-u+1) for u in range(r-1)}               # ab * D_(r-1)
    ok &= (ED == target); print("E(D_r) = ab D_(r-1), r =", r, ED == target)
def Qh(h, n):                                                   # n! [x^n] I_0(2x)^h
    def mul(a, b):
        c = [Fraction(0)]*(n+1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i+j <= n: c[i+j] += x*y
        return c
    I0 = [Fraction(1, factorial(i//2)**2) if i % 2 == 0 else Fraction(0) for i in range(n+1)]
    s = [Fraction(1)] + [Fraction(0)]*n
    for _ in range(h): s = mul(s, I0)
    return int(s[n]*factorial(n))
for r in (3, 5, 7, 9, 15):
    for n in (2, 4, 6, 8):
        lhs = Nodd(r, n); rhs = sum(comb(n, 2*j)*Qh((r-1)//2, n-2*j) for j in range(n//2+1))
        ok &= (lhs == rhs)
print("count identity N_r(n) = sum_j C(n,2j) Q(n-2j): all cells", ok)
print("FIN-OK" if ok else "FALLO")
