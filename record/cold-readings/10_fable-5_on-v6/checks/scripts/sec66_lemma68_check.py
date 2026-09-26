#!/usr/bin/env python3
"""
Referee check for PAPER_OFICIAL_v6.md, section 6.6-6.7 and Corollary 7.8.

(1) Numerical examples after Lemma 7.2 (line 576):
      N_bal(a,3) = 3, 15, 93, 639, 4653  (a = 1..5)
      N_bal(2,q) = 15, 45, 91, 153, 231  (q = 3,5,7,9,11)
    computed from the multinomial closed form of section 6.6 AND by brute force
    from the definition (pairs (xi, eta) with equal multisets).
(2) Lemma 7.2(iii): N_ph(a,q) = N_bal(a+1,q), brute force from the definition.
(3) Lemma 6.8: |Gamma_J| = sum over compatible colourings c of N_1(c) * prod_zeta N_zeta(c).
    Gamma_J is enumerated LITERALLY from [DS, Definition 1.3]:
      (a_1..a_{n+1}) in mu_m^{n+1}, a_i != 1 for all i, and exists J in JJ with
      a_{j_i} a_{k_i} = 1 for i = 1..k (pairs of J not containing 0).
    Elements of mu_m are exponents in Z/m; mu_m = mu_q x mu_r by CRT (e mod q, e mod r).
    For each colouring c (= residues mod r of the exponents), the block-local counts
    N_1(c), N_bal, N_ph are computed BY BRUTE FORCE FROM THEIR DEFINITIONS (with the
    block-local w_0 for the block containing 0), and compared with |Gamma ∩ {colouring c}|.
    The explicit bijection (assemble block-local solutions -> global tuple) is also
    checked as an equality of sets.  Closed forms (Q_{k'-1}(q), multinomial N_bal,
    N_ph = N_bal(a+1)) are compared with the brute-force block counts.
(4) |Gamma_J| is compared with Q_k(m) = N! [x^N] I_0(2x)^{(m-1)/2}.

Predicted resources: < 60 MB, < 40 s.
"""
import itertools, sys, time
from collections import Counter, defaultdict
from fractions import Fraction
from math import factorial
import numpy as np

t_start = time.time()
FAIL = 0
def check(cond, msg):
    global FAIL
    print(("OK   " if cond else "FAIL ") + msg)
    if not cond:
        FAIL += 1

# ---------- closed forms ----------
def multinomial(a, cs):
    r = factorial(a)
    for c in cs:
        r //= factorial(c)
    return r

def compositions(a, parts):
    if parts == 1:
        yield (a,)
        return
    for first in range(a + 1):
        for rest in compositions(a - first, parts - 1):
            yield (first,) + rest

def N_bal_closed(a, q):
    return sum(multinomial(a, cs) ** 2 for cs in compositions(a, q))

def Q(k, m):
    """Q_k(m) = N! [x^N] I_0(2x)^h, N = 2k+2, h = (m-1)//2, exact."""
    N = 2 * k + 2
    h = (m - 1) // 2
    # I_0(2x) = sum_b x^{2b}/(b!)^2, truncated at degree N
    base = [Fraction(0)] * (N + 1)
    for b in range(N // 2 + 1):
        base[2 * b] = Fraction(1, factorial(b) ** 2)
    poly = [Fraction(0)] * (N + 1); poly[0] = Fraction(1)
    for _ in range(h):
        new = [Fraction(0)] * (N + 1)
        for i, ci in enumerate(poly):
            if ci == 0: continue
            for j, cj in enumerate(base):
                if i + j > N: break
                new[i + j] += ci * cj
        poly = new
    val = poly[N] * factorial(N)
    assert val.denominator == 1
    return int(val)

# ---------- brute force definitions of N_bal, N_ph ----------
def N_bal_brute(a, q):
    Om = range(q)
    cnt = 0
    for xi in itertools.product(Om, repeat=a):
        cx = Counter(xi)
        for eta in itertools.product(Om, repeat=a):
            if Counter(eta) == cx:
                cnt += 1
    return cnt

def N_ph_brute(a, q):
    Om = range(q)
    cnt = 0
    for xi in itertools.product(Om, repeat=a + 1):
        cx = Counter(xi)
        for eta in itertools.product(Om, repeat=a):
            ce = Counter(eta)
            if all(ce[u] <= cx[u] for u in ce):
                cnt += 1
    return cnt

print("=== (1) numerical examples after Lemma 7.2 (paper line 576) ===")
vals = [N_bal_closed(a, 3) for a in range(1, 6)]
print("N_bal(a,3), a=1..5, closed form:", vals)
check(vals == [3, 15, 93, 639, 4653], "N_bal(a,3) = 3,15,93,639,4653 (closed form)")
vals_b = [N_bal_brute(a, 3) for a in range(1, 5)]   # a=5 brute force is 3^10 pairs, skip
print("N_bal(a,3), a=1..4, brute force:", vals_b)
check(vals_b == [3, 15, 93, 639], "N_bal(a,3) a=1..4 (brute force)")
vals2 = [N_bal_closed(2, q) for q in (3, 5, 7, 9, 11)]
print("N_bal(2,q), q=3,5,7,9,11, closed form:", vals2)
check(vals2 == [15, 45, 91, 153, 231], "N_bal(2,q) = 15,45,91,153,231 (closed form)")
vals2b = [N_bal_brute(2, q) for q in (3, 5, 7, 9, 11)]
check(vals2b == [15, 45, 91, 153, 231], "N_bal(2,q) (brute force)")
check(N_bal_closed(0, 5) == 1 and N_ph_brute(0, 5) == 5, "N_bal(0,q)=1, N_ph(0,q)=q (used in Cor. 7.8)")

print("=== (2) Lemma 7.2(iii): N_ph(a,q) = N_bal(a+1,q) ===")
for (a, q) in [(0, 3), (1, 3), (2, 3), (3, 3), (0, 5), (1, 5), (2, 5), (1, 7), (2, 7), (1, 9)]:
    nph = N_ph_brute(a, q)
    nb = N_bal_closed(a + 1, q)
    check(nph == nb, f"N_ph({a},{q}) = {nph} = N_bal({a+1},{q}) = {nb}")

# ---------- Lemma 6.8 by brute force ----------
def matchings(elems):
    """all perfect matchings of the list elems, as lists of (a,b) with a<b"""
    if not elems:
        yield []
        return
    a = elems[0]
    for i in range(1, len(elems)):
        b = elems[i]
        rest = elems[1:i] + elems[i + 1:]
        for M in matchings(rest):
            yield [(a, b)] + M

def gamma_DS(m, n):
    """Gamma_J per [DS, Def 1.3], literally.  Returns int array of shape (|Gamma|, n+1),
    entries = exponents in Z/m of a_1..a_{n+1}."""
    k = n // 2
    JJ = list(matchings(list(range(n + 2))))
    assert len(JJ) == np.prod([2 * i + 1 for i in range(k + 1)])
    # all tuples with a_i != 1  -> exponents in 1..m-1, built column by column (int16, low memory)
    L = m - 1
    total = L ** (n + 1)
    E = np.empty((total, n + 1), dtype=np.int16)
    col = np.arange(1, m, dtype=np.int16)
    for j in range(n + 1):
        # column j varies with period L^(n-j) blocks
        rep_inner = L ** (n - j)
        rep_outer = L ** j
        E[:, j] = np.tile(np.repeat(col, rep_inner), rep_outer)
    inG = np.zeros(total, dtype=bool)
    for J in JJ:
        ok = np.ones(total, dtype=bool)
        for (a, b) in J:
            if a == 0:
                continue          # pair containing 0 imposes nothing (Def. 1.3: i = 1..d)
            ok &= ((E[:, a - 1].astype(np.int32) + E[:, b - 1]) % m) == 0
        inG |= ok
    return E[inG].astype(np.int32)

def block_local_count_and_set(c_full, q, r):
    """c_full = (c_0, c_1, ..., c_{n+1}) residues mod r (index 0 included).
    Returns (product of block counts, dict of closed-form counts, set of assembled global
    w-tuples (w_1..w_{n+1}) mod q) for a compatible colouring."""
    idx = range(len(c_full))
    C1 = [i for i in idx if c_full[i] % r == 0]
    reps = range(1, (r - 1) // 2 + 1)
    blocks = []   # list of (kind, data)
    # colour-1 block
    blocks.append(("one", C1))
    for rho in reps:
        A = [i for i in idx if c_full[i] % r == rho]
        B = [i for i in idx if c_full[i] % r == (r - rho) % r]
        blocks.append(("pair", (A, B)))
    Zq = range(q)
    Zq_star = range(1, q)
    per_block_solutions = []   # list of lists of dicts {index: w}
    closed = {}
    for kind, data in blocks:
        sols = []
        if kind == "one":
            C = data
            Cs = [i for i in C if i != 0]
            for ws in itertools.product(Zq_star, repeat=len(Cs)):
                d = dict(zip(Cs, ws))
                if 0 in C:
                    d[0] = (-sum(ws)) % q
                vals = [d[i] for i in C]
                if 0 in vals:
                    continue
                cnt = Counter(vals)
                if all(cnt[v] == cnt[(-v) % q] for v in cnt):
                    sols.append(d)
            kp2 = len(C)
            if kp2 % 2 == 1:
                closed["N_1"] = 0
            elif kp2 == 0:
                closed["N_1"] = 1
            else:
                closed["N_1"] = Q(kp2 // 2 - 1, q)   # Q_{k'-1}(q), |C_1| = 2k'
        else:
            A, B = data
            As = [i for i in A if i != 0]
            Bs = [i for i in B if i != 0]
            for wa in itertools.product(Zq, repeat=len(As)):
                for wb in itertools.product(Zq, repeat=len(Bs)):
                    d = dict(zip(As, wa)); d.update(zip(Bs, wb))
                    if 0 in A or 0 in B:
                        d[0] = (-(sum(wa) + sum(wb))) % q
                    mA = Counter(d[i] for i in A)
                    mB = Counter((-d[l]) % q for l in B)
                    if mA == mB:
                        sols.append(d)
            alpha, beta = len(As), len(Bs)
            if 0 not in A and 0 not in B:
                closed[f"pair{A,B}"] = N_bal_closed(alpha, q) if alpha == beta else 0
            else:
                closed[f"pair{A,B}"] = N_bal_closed(min(alpha, beta) + 1, q)  # N_ph(min) = N_bal(min+1)
        per_block_solutions.append(sols)
    prod = 1
    for s in per_block_solutions:
        prod *= len(s)
    # explicit assembly (bijection)
    n1 = len(c_full) - 1
    assembled = set()
    for combo in itertools.product(*per_block_solutions):
        d = {}
        for part in combo:
            d.update(part)
        # global w_0 must agree with the block-local one (part of the claim)
        w0_global = (-sum(d[i] for i in range(1, n1 + 1))) % q
        assert w0_global == d[0], "block-local w_0 differs from global w_0"
        assembled.add(tuple(d[i] for i in range(1, n1 + 1)))
    return prod, closed, assembled

def crt_pair(e, q, r):
    return (e % q, e % r)

def check_lemma68(m, n, p):
    q = 1
    while m % (q * p) == 0:
        q *= p
    r = m // q
    k = n // 2
    t0 = time.time()
    G = gamma_DS(m, n)
    Qk = Q(k, m)
    check(G.shape[0] == Qk, f"(m,n,p)=({m},{n},{p}): |Gamma_J| = {G.shape[0]} = Q_{k}({m}) = {Qk}  [DS Def 1.3 literal, {time.time()-t0:.1f}s]")
    # group by colouring c = residues mod r of a_1..a_{n+1}
    Cres = (G % r)
    Wres = (G % q)
    groups = defaultdict(set)
    for row_c, row_w in zip(map(tuple, Cres), map(tuple, Wres)):
        groups[row_c].add(row_w)
    # also verify injectivity of (c,w) <-> e  (CRT): sizes must add up
    check(sum(len(s) for s in groups.values()) == G.shape[0], "CRT split is injective (sizes add up)")
    total_pred = 0
    n_compat = 0
    n_bad_blocks = 0
    bad_closed = 0
    reps = range(1, (r - 1) // 2 + 1)
    for c in itertools.product(range(r), repeat=n + 1):
        c0 = (-sum(c)) % r
        cf = (c0,) + c
        C1 = [i for i in range(n + 2) if cf[i] == 0]
        compat = len(C1) % 2 == 0 and all(
            sum(1 for i in range(n + 2) if cf[i] == rho) == sum(1 for i in range(n + 2) if cf[i] == (r - rho) % r)
            for rho in reps)
        actual = groups.get(c, set())
        if not compat:
            if len(actual) != 0:
                n_bad_blocks += 1
                print("FAIL non-compatible colouring with Gamma points:", c)
            continue
        n_compat += 1
        prod, closed, assembled = block_local_count_and_set(cf, q, r)
        closed_prod = 1
        for v in closed.values():
            closed_prod *= v
        if prod != len(actual) or assembled != actual:
            n_bad_blocks += 1
            print("FAIL colouring", c, "product", prod, "actual", len(actual), "assembled==actual", assembled == actual)
        if closed_prod != prod:
            bad_closed += 1
            print("FAIL closed forms vs brute force at colouring", c, closed, prod)
        total_pred += prod
    check(n_bad_blocks == 0, f"(m,n,p)=({m},{n},{p}): every compatible colouring: |Gamma ∩ c| = product of brute-force block counts AND assembled set == Gamma ∩ c  ({n_compat} compatible colourings of {r**(n+1)})")
    check(bad_closed == 0, f"(m,n,p)=({m},{n},{p}): closed forms N_1=Q_{{k'-1}}(q), N_bal multinomial, N_ph=N_bal(a+1) agree with brute-force block counts")
    check(total_pred == G.shape[0], f"(m,n,p)=({m},{n},{p}): sum over compatible colourings = {total_pred} = |Gamma_J| = {G.shape[0]}  (Lemma 6.8)")
    print(f"   [{time.time()-t0:.1f}s]")

print("=== (3)+(4) Lemma 6.8 by brute force from [DS, Def 1.3] ===")
for (m, n, p) in [(15, 2, 3), (15, 2, 5), (21, 2, 3), (21, 2, 7), (45, 2, 3), (45, 2, 5),
                  (105, 2, 3), (105, 2, 5), (105, 2, 7), (15, 4, 3), (15, 4, 5), (21, 4, 3), (21, 4, 7)]:
    check_lemma68(m, n, p)

print("=== Corollary 7.8 colourings: block data ===")
# balanced: n=2a, a coords zeta, a coords zeta^{-1}, one coord 1  -> c_0 = 1, C_1 = {0,s}
# phantom : n=2a, a+1 coords zeta, a coords zeta^{-1}            -> c_0 = zeta^{-1}, C_1 = {}
for a in (1, 2):
    r = 5
    n = 2 * a
    c = (1,) * a + (r - 1,) * a + (0,)
    c0 = (-sum(c)) % r
    check(c0 == 0, f"Cor 7.8 balanced colouring a={a}: c_0 = 1 (residue {c0})")
    c = (1,) * (a + 1) + (r - 1,) * a
    c0 = (-sum(c)) % r
    check(c0 == r - 1, f"Cor 7.8 phantom colouring a={a}: c_0 = zeta^-1 (residue {c0} = -1 mod {r})")

print(f"TOTAL FAILURES: {FAIL}   wall {time.time()-t_start:.1f}s")
