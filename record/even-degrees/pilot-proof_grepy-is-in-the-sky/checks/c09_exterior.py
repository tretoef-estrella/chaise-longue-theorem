# c09_exterior.py — pilot. Gate for the proof of (M1) in the exterior algebra  Lambda(Z^r),  basis v_0..v_{r-1},  r = 2h+1.
#   e_a = v_{2a} (a = 0..h),  o_b = v_{2b+1} (b = 0..h-1),   J_sigma = sum_{a+b=sigma} e_a ^ o_b   (sigma = 0..2h-1)
#   L(z) = sum_{sigma < h} J_sigma z^sigma,   U(z) = sum_{sigma >= h} J_sigma z^(sigma-h),   E(z) = sum_a e_a z^a
# Exact integer arithmetic. Checked for each r:
#   (1) J_sigma is the 2-form of the polynomial omega_{2 sigma + 1}: in particular J_{h-1} <-> B = D_{r-1}, and for sigma >= h
#       the polynomial is b^i D_r(a,b) with i = 2(sigma - h) + 1   (dictionary, checked on the coefficients)
#   (2) gamma_n(L + z^h U) = 0 for n >= 2 and E ^ (L + z^h U) = 0                       (decomposability)
#   (3) the recursion gamma_n(L) = - sum_{j=1..n} z^(hj) gamma_{n-j}(L) gamma_j(U)
#   (4) for every t >= 1:  gamma_{t+1}(J_{h-1})  is an INTEGER combination of the elements J_sigma0 ^ (divided-power monomial of degree t
#       in the J_sigma, sigma >= h), sigma0 < h;  and  e_h ^ gamma_t(J_{h-1})  is an integer combination of v_i ^ (such monomials of degree t).
#       (4) is checked by producing the combination from the recursion and comparing both sides.
# Usage: c09_exterior.py r
import sys, itertools
from collections import defaultdict

def wedge(x, y):
    out = defaultdict(int)
    for A, ca in x.items():
        for B, cb in y.items():
            if set(A) & set(B): continue
            merged = A + B
            # sign of the permutation sorting `merged`
            inv = sum(1 for i in range(len(merged)) for j in range(i + 1, len(merged)) if merged[i] > merged[j])
            out[tuple(sorted(merged))] += (-1) ** inv * ca * cb
    return {k: v for k, v in out.items() if v}

def add(x, y, c=1):
    out = defaultdict(int)
    for k, v in x.items(): out[k] += v
    for k, v in y.items(): out[k] += c * v
    return {k: v for k, v in out.items() if v}

ONE = {(): 1}

def gamma_terms(terms, k):
    """Divided power: sum over the k-subsets of a list of terms (each a one-monomial 2-form)."""
    out = {}
    for sub in itertools.combinations(terms, k):
        w = ONE
        for tm in sub: w = wedge(w, tm)
        out = add(out, w)
    return out

# polynomials in z with exterior coefficients: dict power -> form
def padd(P, Q, c=1):
    out = dict(P)
    for k, v in Q.items():
        out[k] = add(out.get(k, {}), v, c)
        if not out[k]: del out[k]
    return out

def pmul(P, Q, shift=0):
    out = {}
    for i, x in P.items():
        for j, y in Q.items():
            w = wedge(x, y)
            if w:
                out[i + j + shift] = add(out.get(i + j + shift, {}), w)
                if not out[i + j + shift]: del out[i + j + shift]
    return out

def main(r):
    h = (r - 1) // 2
    e = lambda a: 2 * a
    o = lambda b: 2 * b + 1
    Jterms = {s: [{tuple(sorted((e(a), o(s - a)))): (1 if e(a) < o(s - a) else -1)} for a in range(0, h + 1) if 0 <= s - a <= h - 1] for s in range(2 * h)}
    J = {s: gamma_terms(Jterms[s], 1) for s in range(2 * h)}
    # (1) dictionary: J_sigma = sum_{u<u', u+u'=2 sigma+1} (-1)^u v_u ^ v_u'
    ok1 = all(J[s] == {(u, 2 * s + 1 - u): (-1) ** u for u in range(0, r) if u < 2 * s + 1 - u <= r - 1} for s in range(2 * h))
    # terms of L and U with their z-degree
    Lterms = [(s, tm) for s in range(h) for tm in Jterms[s]]
    Uterms = [(s - h, tm) for s in range(h, 2 * h) for tm in Jterms[s]]
    def gam(terms, k):
        out = {}
        for sub in itertools.combinations(terms, k):
            w = ONE; d = 0
            for (dz, tm) in sub:
                w = wedge(w, tm); d += dz
                if not w: break
            if w:
                out[d] = add(out.get(d, {}), w)
                if not out[d]: del out[d]
        return out
    Jall = [(s, tm) for s in range(2 * h) for tm in Jterms[s]]
    nmax = h + 1
    ok2 = all(gam(Jall, n) == {} for n in range(2, nmax + 1))
    Ez = {a: {(e(a),): 1} for a in range(h + 1)}
    ok2 = ok2 and pmul(Ez, gam(Jall, 1)) == {}
    gL = {n: gam(Lterms, n) for n in range(0, nmax + 1)}
    gU = {n: gam(Uterms, n) for n in range(0, nmax + 1)}
    ok3 = True
    for n in range(2, nmax + 1):
        rhs = {}
        for j in range(1, n + 1):
            rhs = padd(rhs, pmul(gL[n - j], gU[j], shift=h * j), -1)
        ok3 = ok3 and (rhs == gL[n])
    # (4) unroll: gamma_n(L) = z^(h(n-1)) L ^ A_{n-1} + z^(hn) A'_n with A, A' built from the gamma_j(U) only
    A = {0: {0: ONE}}; Ap = {0: {0: ONE}, 1: {}}
    for n in range(2, nmax + 1):
        An = {}; Apn = {}
        for j in range(1, n):
            An = padd(An, pmul(A[n - j - 1], gU[j]), -1)
            Apn = padd(Apn, pmul(Ap[n - j], gU[j]), -1)
        Apn = padd(Apn, gU[n], -1)
        A[n - 1] = An; Ap[n] = Apn
    ok4 = True; lines = []
    for t in range(1, h + 1):
        # (4a): gamma_{t+1}(J_{h-1}) = coefficient of z^((t+1)(h-1)) in z^(ht) L ^ A_t
        lhs = gamma_terms(Jterms[h - 1], t + 1)
        rhs = pmul(gL[1], A[t], shift=h * t).get((t + 1) * (h - 1), {}) if t in A else {}
        full = padd(pmul(gL[1], A[t], shift=h * t), {k + h * (t + 1): v for k, v in Ap[t + 1].items()}) if t + 1 in Ap else None
        a_ok = (lhs == rhs) and (full is None or full == gL[t + 1])
        # (4b): e_h ^ gamma_t(J_{h-1}) = coefficient of z^(h + t(h-1)) in  z^(ht) E ^ ( -U ^ A_{t-1} + A'_t )
        lhs_b = wedge({(e(h),): 1}, gamma_terms(Jterms[h - 1], t))
        inner = padd(pmul(gU[1], A[t - 1]), Ap[t], -1)        # U ^ A_{t-1} - A'_t
        rhs_b = pmul(Ez, inner, shift=h * t).get(h + t * (h - 1), {})
        rhs_b = {k: -v for k, v in rhs_b.items()}
        b_ok = (lhs_b == rhs_b)
        ok4 = ok4 and a_ok and b_ok
        lines.append(f"t={t}: (4a) {a_ok} [{len(lhs)} monomials], (4b) {b_ok} [{len(lhs_b)} monomials]")
    print(f"EXTERIOR r={r} (h={h}): dictionary {ok1}; decomposability {ok2}; recursion {ok3}; identities (4): {ok4}  --  " + "; ".join(lines), flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]))
