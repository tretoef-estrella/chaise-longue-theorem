"""
block_compare.py — two independent checks of §6 at the level of individual colourings.

(A) Enumerate Γ_𝒥 ⊆ μ_m^{n+1} directly from [DS, Definition 1.3] (a_i ≠ 1 for i = 1..n+1, and some matching J with
    a_{j_i} a_{k_i} = 1 for i ≥ 1), split the tuples by their colouring c = (a_i mod μ_q) ∈ μ_r^{n+1} (via μ_m = μ_q × μ_r),
    and compare the per-colouring counts with the paper's block product of Lemma 6.8 (implemented here from the
    DEFINITIONS of N_1, N_bal, N_ph: with 0 counted in its class, the colour-1 block contributes the number of
    |𝒞_1|-tuples in μ_q∖{1} closed under inversion, a pair block {ζ, ζ^{-1}} of sizes (a, b) contributes
    N_bal(a,q) if a = b and 0 ∉ block, N_ph(min(a,b), q) if 0 ∈ block and |a − b| = 1, else 0).
(B) Parse the per-orbit dimensions dim π_c(I) computed by crt_colouring_k2.py (logs) and compare them with the same
    block product: this tests Proposition 6.5 + Lemmas 6.6, 6.7 + Corollary 7.8 (equality) colouring by colouring.

usage: python3 block_compare.py m p k logfile
"""
import sys, itertools, re
from math import factorial
from collections import Counter

def matchings(N):
    idx = list(range(N))
    def rec(rest):
        if not rest:
            yield []; return
        a = rest[0]
        for b in rest[1:]:
            r2 = [x for x in rest if x not in (a, b)]
            for mm in rec(r2):
                yield [(a, b)] + mm
    return list(rec(idx))

def N_bal(a, q):
    # number of pairs of a-tuples in a q-set with equal multisets = Σ over compositions (a!/Πc_i!)^2
    tot = 0
    def rec(i, rem, acc):
        nonlocal tot
        if i == q - 1:
            tot += (acc // factorial(rem)) ** 2 if True else 0
            return
        for c in range(rem + 1):
            rec(i + 1, rem - c, acc // factorial(c))
    rec(0, a, factorial(a))
    return tot

def N_ph(a, q):
    # pairs (ξ, η) ∈ Ω^{a+1} × Ω^a with multiset(η) ⊆ multiset(ξ): brute force for small a, else via Lemma-free count
    Om = range(q); tot = 0
    for xi in itertools.product(Om, repeat=a + 1):
        cx = Counter(xi)
        for eta in itertools.product(Om, repeat=a):
            ce = Counter(eta)
            if all(ce[u] <= cx[u] for u in ce):
                tot += 1
    return tot

def closed_tuples(n, q):
    """number of n-tuples in μ_q∖{1} (as Z/q ∖ {0}) whose multiset is closed under inversion (negation)"""
    tot = 0
    for t in itertools.product(range(1, q), repeat=n):
        c = Counter(t)
        if all(c[u] == c[(-u) % q] for u in c):
            tot += 1
    return tot

def block_product(e, r, q, k, cache):
    """e = exponents (e_1..e_{n+1}) of the colouring; e_0 = -Σ e mod r"""
    n1 = len(e)
    e0 = (-sum(e)) % r
    full = [e0] + list(e)           # index 0 first
    classes = Counter(full)
    prod = 1
    # colour 1
    s1 = classes.get(0, 0)
    if s1 % 2:
        return 0
    key = ('c1', s1)
    if key not in cache:
        cache[key] = closed_tuples(s1, q) if s1 > 0 else 1
    prod *= cache[key]
    # pairs
    for z in range(1, (r + 1) // 2):
        a = classes.get(z, 0); b = classes.get((-z) % r, 0)
        zero_in = (e0 == z) or (e0 == (-z) % r)
        if not zero_in:
            if a != b:
                return 0
            key = ('bal', a)
            if key not in cache:
                cache[key] = N_bal(a, q)
            prod *= cache[key]
        else:
            # sizes counted WITH 0; the block with 0 has one more index; α, β = sizes without 0
            if e0 == z:
                alpha, beta = a - 1, b
            else:
                alpha, beta = a, b - 1
            if abs(alpha - beta) != 1:
                return 0
            key = ('ph', min(alpha, beta))
            if key not in cache:
                cache[key] = N_ph(min(alpha, beta), q)
            prod *= cache[key]
    return prod

def main():
    m, p, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    logfile = sys.argv[4] if len(sys.argv) > 4 else None
    q = p
    while m % (q * p) == 0:
        q *= p
    r = m // q; n1 = 2 * k + 1; N = 2 * k + 2
    Js = matchings(N)
    cache = {}
    # (A) enumerate Γ_𝒥 directly, colouring by colouring (a ∈ (Z/m)^{n+1}, additive notation; a_i ≠ 0)
    # colouring: the μ_r-component of a is a mod r ... careful: Z/m ≅ Z/q × Z/r by CRT; the μ_r-part of exp a is a mod r.
    pairs_noz = [[(j, kk) for (j, kk) in J if j != 0] for J in Js]
    per_col = Counter(); total = 0
    print(f"(A) enumerating Γ_J for m={m}, n={2*k}: {m**n1} tuples ...", flush=True)
    for a in itertools.product(range(1, m), repeat=n1):
        ok = False
        for P in pairs_noz:
            if all((a[j - 1] + a[kk - 1]) % m == 0 for (j, kk) in P):
                ok = True; break
        if ok:
            total += 1
            e = tuple(x % r for x in a)
            per_col[e] += 1
    print(f"(A) |Γ_J| = {total}; colourings with points: {len(per_col)}")
    # compare with block products over ALL colourings
    bad = 0; s = 0
    for e in itertools.product(range(r), repeat=n1):
        pred = block_product(e, r, q, k, cache)
        s += pred
        if pred != per_col.get(e, 0):
            bad += 1
            if bad <= 5:
                print("   (A) mismatch", e, "enumerated", per_col.get(e, 0), "block product", pred)
    print(f"(A) Σ_c block products = {s} vs |Γ_J| = {total}: {'AGREES' if s == total else 'DISAGREES'}; per-colouring mismatches: {bad}")
    if logfile:
        txt = open(logfile).read()
        rx = re.compile(r"rep=\(([^)]*)\) mult=(\d+) surviving gens=(\d+) dim=(\d+)")
        seen = {}
        for mm in rx.finditer(txt):
            rep = tuple(int(x) for x in mm.group(1).replace(' ', '').split(',') if x != '')
            seen[rep] = int(mm.group(4))
        rx2 = re.compile(r"audit e=\(([^)]*)\) dim=(\d+)")
        for mm in rx2.finditer(txt):
            rep = tuple(int(x) for x in mm.group(1).replace(' ', '').split(',') if x != '')
            seen[rep] = int(mm.group(2))
        bad = 0
        for rep, dim in seen.items():
            pred = block_product(rep, r, q, k, cache)
            enum = per_col.get(rep, 0)
            if not (pred == dim == enum):
                bad += 1
                print("   (B) mismatch", rep, "engine dim", dim, "block product", pred, "enumerated", enum)
        print(f"(B) {len(seen)} colourings/orbit representatives from {logfile}: engine dim == block product == enumerated count in all but {bad}")

if __name__ == '__main__':
    main()
