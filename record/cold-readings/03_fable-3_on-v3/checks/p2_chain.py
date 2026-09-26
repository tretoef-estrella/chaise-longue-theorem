"""Prop 5.6 (P2): for mu <= mu~ in Par_m (weak dominance), opt_p(mu) <= opt_p(mu~) for every position p = 1..q-1.
Own code. Exhaustive for all comparable pairs in Par_m, m <= M, at given h (q = 2h+1); plus random sampling at large h."""
import sys, random, itertools, time
sys.path.insert(0, __file__.rsplit('/',1)[0])
from p3_slices import partitions_upto, preceq, options

def check(m, h, verbose=False):
    q = 2*h + 1
    P = partitions_upto(m, h)
    opts = {mu: options(mu, q) for mu in P}
    fails = 0; pairs = 0
    for mu in P:
        for nu in P:
            if preceq(mu, nu):
                pairs += 1
                om, on = opts[mu], opts[nu]
                for p in range(q - 1):
                    if not preceq(om[p], on[p]):
                        fails += 1
                        if verbose: print("  FAIL", mu, nu, "position", p+1, om[p], on[p])
    return pairs, fails

if __name__ == '__main__':
    t0 = time.time()
    for h, M in [(1, 16), (2, 16), (3, 14), (4, 14), (7, 13), (13, 12), (40, 12), (60, 12)]:
        tot = 0; f = 0
        for m in range(0, M + 1):
            pr, fl = check(m, h); tot += pr; f += fl
        print(f"h={h} (q={2*h+1}), m<={M}: comparable pairs={tot}, failures={f}  [{time.time()-t0:.0f}s]")
    # random large h: partitions of size <= 30 with length <= h, h = 200 (q = 401): exhaustive pairs among a random sample
    random.seed(1)
    h = 200; q = 401
    P = partitions_upto(30, h)  # all partitions of size <= 30 with parity 30 (even sizes)
    P += partitions_upto(29, h)
    S = random.sample(P, 600)
    tot = 0; f = 0
    for mu in S:
        om = options(mu, q)
        for nu in S:
            if preceq(mu, nu):
                tot += 1; on = options(nu, q)
                for p in range(q - 1):
                    if not preceq(om[p], on[p]): f += 1
    print(f"h={h} (q={q}), random 600 partitions of size <= 30: comparable pairs={tot}, failures={f}  [{time.time()-t0:.0f}s]")
