"""
prop74_check.py — brute-force check, from the DEFINITIONS of §7.2-7.4, of
  (P1)  the fibre rule: adding a value u at a peeled x-index changes the shape (λ_+, λ_-) of the tail as
        u = v_j (residual value of R_-) -> (λ_+, λ_- - e_j); u = u_j (of R_+) -> (λ_+ + e_j, λ_-); other -> (λ_+ ⊔ 1, λ_-);
  (Chain) Lemma 7.3: opt_1 ≼ opt_2 ≼ ... ≼ opt_q in the product of weak dominance orders;
  (P2)  Proposition 7.4: μ ≼ μ~ implies opt_p(μ) ≼ opt_p(μ~) for every position p;
  (7.1) the coverage formula for every down-set Λ (small cells only).
Referee's own code. usage: python3 prop74_check.py  (cells hard-coded below)
"""
import itertools, sys, time
from collections import Counter

def partitions_upto(n, maxlen):
    """all partitions of size <= n with at most maxlen parts (as tuples, decreasing)"""
    out = [()]
    def rec(rem, maxpart, cur):
        if rem == 0:
            return
        for part in range(min(rem, maxpart), 0, -1):
            new = cur + (part,)
            if len(new) <= maxlen:
                out.append(new)
                rec(rem - part, part, new)
    rec(n, n, ())
    return list(set(out))

def S(lam, t):
    return sum(lam[:t])

def dom(lam, mu):
    """weak dominance lam ≼ mu: S_t(lam) <= S_t(mu) for all t"""
    T = max(len(lam), len(mu), 1)
    return all(S(lam, t) <= S(mu, t) for t in range(1, T + 1))

def bdom(a, b):
    return dom(a[0], b[0]) and dom(a[1], b[1])

def bpar(alpha, beta, q):
    out = []
    for lp in partitions_upto(alpha, q):
        for lm in partitions_upto(beta, q):
            if sum(lp) - sum(lm) == alpha - beta and sum(lp) + sum(lm) <= alpha + beta and len(lp) + len(lm) <= q:
                out.append((lp, lm))
    return out

def sort_desc(lst):
    return tuple(sorted([x for x in lst if x > 0], reverse=True))

def options(mu, q):
    """the q options opt_1..opt_q of §7.3 for a tail shape mu = (mu_+, mu_-)"""
    mp, mm = mu
    lp, lm = len(mp), len(mm)
    opts = []
    for p in range(1, lm + 1):              # removals from mu_-
        lst = list(mm); lst[p - 1] -= 1
        opts.append((mp, sort_desc(lst)))
    for _ in range(q - lp - lm):            # middle
        opts.append((sort_desc(list(mp) + [1]), mm))
    for j in range(lp, 0, -1):              # additions to mu_+ (j = lp first ... j = 1 last)
        lst = list(mp); lst[j - 1] += 1
        opts.append((sort_desc(lst), mm))
    assert len(opts) == q
    return opts

def shape(xi, eta):
    X = Counter(xi); Y = Counter(eta)
    rp = [X[u] - Y[u] for u in set(X) | set(Y) if X[u] > Y[u]]
    rm = [Y[u] - X[u] for u in set(X) | set(Y) if Y[u] > X[u]]
    return (sort_desc(rp), sort_desc(rm))

def check_P1(alpha, beta, q):
    """every tail: the multiset of shapes obtained by adding each u in Omega equals the multiset of options"""
    Om = range(q); bad = 0; n = 0
    for tail_x in itertools.product(Om, repeat=alpha - 1):
        for eta in itertools.product(Om, repeat=beta):
            mu = shape(tail_x, eta)
            got = Counter(shape((u,) + tail_x, eta) for u in Om)
            exp = Counter(options(mu, q))
            n += 1
            if got != exp:
                bad += 1
                if bad <= 3:
                    print("   P1 FAIL", tail_x, eta, mu, got, exp)
    return n, bad

def check_chain_P2(alpha, beta, q):
    B = bpar(alpha - 1, beta, q)
    chain_bad = 0
    for mu in B:
        o = options(mu, q)
        for i in range(q - 1):
            if not bdom(o[i], o[i + 1]):
                chain_bad += 1
        # membership
        for x in o:
            assert x in set(bpar(alpha, beta, q)) or True
    pairs = 0; bad = 0
    Bset = set(bpar(alpha, beta, q))
    for mu in B:
        omu = options(mu, q)
        for x in omu:
            assert x in Bset, (mu, x)
        for nu in B:
            if mu != nu and bdom(mu, nu):
                pairs += 1
                onu = options(nu, q)
                for p in range(q):
                    if not bdom(omu[p], onu[p]):
                        bad += 1
                        if bad <= 5:
                            print("   P2 FAIL", mu, nu, "p=", p + 1, omu[p], onu[p])
    return len(B), chain_bad, pairs, bad

def downsets(P):
    """all down-sets of the poset P (list) under bdom; via antichains -> down-closure (small posets only)"""
    P = list(P)
    below = {x: frozenset(y for y in P if bdom(y, x)) for x in P}
    # enumerate down-sets by adding elements in a linear extension
    order = sorted(P, key=lambda x: (sum(x[0]) + sum(x[1]), x))
    res = set([frozenset()])
    for x in order:
        new = set()
        for D in res:
            if below[x] - {x} <= D:
                new.add(D | {x})
        res |= new
    return res

def check_71(alpha, beta, q, maxsets=3000):
    P = bpar(alpha, beta, q)
    Ds = downsets(P)
    if len(Ds) > maxsets:
        return len(Ds), None
    B = bpar(alpha - 1, beta, q)
    bad = 0
    for L in Ds:
        for mu in B:
            o = options(mu, q)
            F = sum(1 for x in o if x in L)
            # formula (7.1)
            mp, mm = mu; lp, lm = len(mp), len(mm)
            inL = [x in L for x in o]
            # initial segment?
            if any(inL[i] and not inL[i - 1] for i in range(1, q)):
                bad += 1; print("   not an initial segment", L, mu); continue
            r = sum(1 for i in range(lm) if inL[i])
            iota = 1 if (q - lp - lm > 0 and inL[lm]) else 0
            adds = [inL[q - j] for j in range(1, lp + 1)]  # position q+1-j -> index q-j ; j = 1..lp
            js = [j for j in range(1, lp + 1) if adds[j - 1]]
            j0 = min(js) if js else None
            formula = r + (q - lp - lm) * iota + ((lp - j0 + 1) if j0 else 0)
            if formula != F:
                bad += 1; print("   (7.1) FAIL", L, mu, F, formula)
    return len(Ds), bad

if __name__ == '__main__':
    t0 = time.time()
    print("== (P1) fibre rule, brute force over all tails ==")
    for (a, b, q) in [(2, 1, 3), (2, 2, 3), (3, 2, 3), (2, 1, 5), (2, 2, 5), (3, 2, 5), (2, 2, 7), (2, 1, 9), (3, 1, 9), (2, 2, 9)]:
        n, bad = check_P1(a, b, q)
        print(f"  (alpha,beta,q)=({a},{b},{q}): {n} tails, {bad} failures")
    print("== (Chain) Lemma 7.3 and (P2) Proposition 7.4 over all comparable pairs ==")
    for (a, b, q) in [(4, 4, 3), (5, 3, 3), (6, 6, 3), (7, 5, 3), (4, 4, 5), (5, 4, 5), (6, 5, 5), (4, 4, 7), (5, 5, 7), (3, 3, 9), (5, 5, 9), (6, 4, 9), (4, 4, 11), (8, 7, 5), (7, 7, 3), (9, 8, 3), (4, 3, 27)]:
        nB, cb, pairs, bad = check_chain_P2(a, b, q)
        print(f"  (alpha,beta,q)=({a},{b},{q}): |BPar(alpha-1,beta)|={nB}, chain failures {cb}, comparable pairs {pairs}, P2 failures {bad}  [{time.time()-t0:.1f}s]", flush=True)
    print("== (7.1) coverage formula over all down-sets (small cells) ==")
    for (a, b, q) in [(2, 1, 3), (2, 2, 3), (3, 2, 3), (3, 3, 3), (2, 1, 5), (2, 2, 5), (3, 2, 5), (2, 2, 7), (3, 1, 9), (2, 2, 9)]:
        nD, bad = check_71(a, b, q)
        print(f"  (alpha,beta,q)=({a},{b},{q}): {nD} down-sets, failures {bad}  [{time.time()-t0:.1f}s]", flush=True)
    print("DONE")
