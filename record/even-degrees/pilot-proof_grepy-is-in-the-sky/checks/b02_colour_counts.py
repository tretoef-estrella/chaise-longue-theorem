# b02_colour_counts.py — pilot. Gate for B3/B4: the count |Gamma| of an EVEN m = q*r' (q = p^v, p not dividing r') factors over the
# colourings by r'-th roots of unity as  sum_c N_1(c) * N_{-1}(c) * prod_zeta N_zeta(c)  with
#   colour 1 block (size n1):   p odd: Q^[(q-1)/2](n1)  (fixed-point-free);   p = 2: N_{q-1}(n1) (inversion on mu_q \ 1 fixes -1; =1 or 0 if q = 2)
#   colour -1 block (size n2; exists only if r' is even, i.e. p odd):  N_q(n2)  (inversion on mu_q fixes 1)
#   a pair of inverse colours zeta != +-1:  N_bal(a, q) if 0 is not in the block and both classes have a elements;
#                                           N_bal(a+1, q) if 0 is in the block and both classes have a+1 elements (index 0 counted)
# and it is compared with |Gamma| counted from the definition of [DS] and with N_{m-1}(2k+2).
import sys, itertools
from eng import matchings, N_odd, Q_free
from b01_theoremC_even import N_bal

def gamma_def(k, m):
    n1 = 2 * k + 1
    Js = [[(a, b) for (a, b) in J if a != 0] for J in matchings(range(n1 + 1))]
    cnt = 0
    for a in itertools.product(range(1, m), repeat=n1):
        for J in Js:
            if all((a[x - 1] + a[y - 1]) % m == 0 for (x, y) in J):
                cnt += 1; break
    return cnt

def colour_sum(k, m, p):
    q = 1
    while (m // q) % p == 0: q *= p
    rp = m // q
    n1 = 2 * k + 1
    total = 0; ncomp = 0
    for c in itertools.product(range(rp), repeat=n1):
        c0 = (-sum(c)) % rp
        col = (c0,) + c                       # colours of the indices 0..n1, additive notation: colour x means zeta^x
        cls = [[i for i in range(n1 + 1) if col[i] == x] for x in range(rp)]
        prodv = 1
        # colour 1
        s1 = len(cls[0])
        if s1 % 2: continue
        if p == 2:
            prodv *= N_odd(q - 1, s1) if q > 2 else 1
        else:
            prodv *= Q_free((q - 1) // 2, s1)
        # colour -1
        if rp % 2 == 0:
            s2 = len(cls[rp // 2])
            if s2 % 2: continue
            prodv *= N_odd(q, s2)
        ok = True
        for x in range(1, rp):
            y = (-x) % rp
            if x >= y: continue
            if len(cls[x]) != len(cls[y]): ok = False; break
            a = len(cls[x])
            if a:
                prodv *= N_bal(a, q)          # 0 in the block: N_ph(a-1, q) = N_bal(a, q) as well
        if not ok: continue
        total += prodv; ncomp += 1
    return total, ncomp, q, rp

if __name__ == "__main__":
    cells = [(1, 6, 2), (1, 6, 3), (2, 6, 2), (2, 6, 3), (1, 10, 2), (1, 10, 5), (2, 10, 2), (2, 10, 5), (1, 12, 2), (1, 12, 3), (2, 12, 2), (2, 12, 3),
             (1, 20, 2), (1, 20, 5), (1, 18, 2), (1, 18, 3), (1, 30, 2), (1, 30, 3), (1, 30, 5), (3, 6, 2), (3, 6, 3)]
    allok = True
    for (k, m, p) in cells:
        tot, ncomp, q, rp = colour_sum(k, m, p)
        g = gamma_def(k, m) if (m - 1) ** (2 * k + 1) <= 400000 else None
        f = N_odd(m - 1, 2 * k + 2)
        ok = (tot == f) and (g is None or g == f)
        allok &= ok
        print(f"k={k} m={m} p={p} (q={q}, r'={rp}): sum over {ncomp} compatible colourings={tot}  |Gamma| by definition={g}  N_(m-1)(2k+2)={f}  agree={ok}", flush=True)
    print("ALL AGREE" if allok else "SOME DISAGREE")
