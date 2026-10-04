# fria_gate4.py — cold audit, gate G4: the colour reduction for EVEN m (B3, B4 of REPORT.md), from the literal generators psi_J of [DS],
# colouring by colouring, with Groebner bases in Singular over a finite field containing mu_{r'}. Own code (Grepy Chats, 2 Oct 2026).
# Prediction for a compatible colouring c:  N^(1)(|C_1|) * N^(-1)(|C_{-1}|) * prod_zeta N_bal(|C_zeta|, q);  0 if not compatible.
import sys, itertools, subprocess, math
from fractions import Fraction
from collections import Counter

def series_pow(coefs, e, n):          # (sum coefs[i] x^i)^e truncated at x^n
    out = [Fraction(1)] + [Fraction(0)] * n
    for _ in range(e):
        new = [Fraction(0)] * (n + 1)
        for i, a in enumerate(out):
            if a == 0: continue
            for j, b in enumerate(coefs):
                if i + j > n: break
                new[i + j] += a * b
        out = new
    return out
def N_closed(size, nvals_classes, fixed, n):   # n-tuples in a set with `nvals_classes` classes {u,-u} and `fixed` (0 or 1) fixed points, splitting into pairs
    I0 = [Fraction(1, math.factorial(b) ** 2) if True else 0 for b in range(n // 2 + 1)]
    I0x = [Fraction(0)] * (n + 1)
    for b in range(n // 2 + 1): I0x[2 * b] = I0[b]
    s = series_pow(I0x, nvals_classes, n)
    if fixed:
        ch = [Fraction(0)] * (n + 1)
        for b in range(n // 2 + 1): ch[2 * b] = Fraction(1, math.factorial(2 * b))
        s = [sum(s[i] * ch[d - i] for i in range(d + 1)) for d in range(n + 1)]
    v = s[n] * math.factorial(n); assert v.denominator == 1
    return int(v)
def N_bal(a, q):
    e = [Fraction(1, math.factorial(c) ** 2) for c in range(a + 1)]
    v = series_pow(e, q, a)[a] * math.factorial(a) ** 2; assert v.denominator == 1
    return int(v)
def matchings(S):
    S = list(S)
    if not S: yield (); return
    a = S[0]
    for i in range(1, len(S)):
        for M in matchings(S[1:i] + S[i + 1:]): yield ((a, S[i]),) + M

def predict(c, q, rp, p):
    c0 = (-sum(c)) % rp; cl = Counter([c0] + list(c)); val = 1
    for z in range(rp):
        zi = (-z) % rp; nz = cl.get(z, 0)
        if z == zi:
            if nz % 2: return 0
            if z == 0:
                val *= N_closed(None, (q - 1) // 2 if q % 2 else (q - 2) // 2, 0 if q % 2 else 1, nz)   # tuples in mu_q minus 1
            else:
                val *= N_closed(None, (q - 1) // 2, 1, nz)                                               # colour -1 (p odd): tuples in mu_q
        elif z < zi:
            if nz != cl.get(zi, 0): return 0
            val *= N_bal(nz, q)
    return val

def run_cell(k, m, p):
    n1 = 2 * k + 1; q = 1
    while m % (q * p) == 0: q *= p
    rp = m // q
    # field containing mu_{r'}
    e = 1
    while (p ** e - 1) % rp: e += 1
    order = p ** e - 1
    field = f"{p}" if e == 1 else f"({p**e},a)"
    def root(z):
        if e == 1:
            # primitive element of F_p
            g = next(g for g in range(2, p) if all(pow(g, order // f, p) != 1 for f in range(2, order + 1) if order % f == 0)) if p > 2 else 1
            return str(pow(g, (order // rp) * z, p))
        return f"a^{(order // rp) * z}" if z else "1"
    reps = {}
    for c in itertools.product(range(rp), repeat=n1):
        key = tuple(sorted(c)); reps[key] = reps.get(key, 0) + 1
    J = list(matchings(range(n1 + 1)))
    lines = [f"ring R = {field},(t(1..{n1})),dp;", "option(redSB);",
             f"proc phi(poly u, ideal G) {{ poly s = 0; poly w = 1; int e; for (e = 0; e < {m}; e++) {{ s = s + w; w = reduce(w*u, G); }} return(s); }}"]
    for key in reps:
        box = ",".join(f"(t({i+1})-({root(z)}))^{q}" for i, z in enumerate(key))
        lines.append(f"ideal G = std(ideal({box}));")
        gens = []
        for M in J:
            fac = []
            for (a, b) in M:
                if a == 0: fac.append(f"(t({b})-1)")
                else: fac.append(f"(t({b})-1)*phi(t({a})*t({b}),G)")
            gens.append("reduce(" + "*".join(fac) + ",G)")
        lines.append("ideal I = " + ",".join(gens) + ";")
        lines.append(f'print("DIM " + string({q**n1} - vdim(std(I+G))));')
        lines.append("kill I; kill G;")
    lines.append('print("SINGULAR-END"); quit;')
    out = subprocess.run(["Singular", "-q"], input="\n".join(lines), capture_output=True, text=True).stdout
    dims = [int(x.split()[1]) for x in out.splitlines() if x.startswith("DIM ")]
    assert "SINGULAR-END" in out and len(dims) == len(reps), out[-2000:]
    bad = 0; total = 0; nonzero = 0
    for (key, mult), d in zip(reps.items(), dims):
        pr = predict(key, q, rp, p); total += mult * d; nonzero += (d > 0)
        if pr != d: bad += 1; print(f"   mismatch k={k} m={m} p={p} colouring {key}: measured {d}, predicted {pr}")
    G = N_closed(None, (m - 2) // 2, 1, 2 * k + 2)
    print(f"(k,m,p)=({k},{m},{p}): q={q}, r'={rp}, field GF({p**e}); colouring types {len(reps)} ({rp**n1} colourings), with non-zero ideal {nonzero}; mismatches with the block prediction {bad}; sum over colourings {total}; |Gamma| = N_{m-1}({2*k+2}) = {G}; equal {total == G}", flush=True)
    return bad, total == G

allbad = 0; alleq = True
for a in sys.argv[1:]:
    k, m, p = (int(x) for x in a.split(','))
    b, eq = run_cell(k, m, p); allbad += b; alleq = alleq and eq
print(f"TOTAL mismatches {allbad}; all sums equal |Gamma|: {alleq}"); print("FIN-OK")
