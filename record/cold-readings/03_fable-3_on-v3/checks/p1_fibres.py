"""P1 (§5.4) and formula (5.1) (§5.5) tested directly, own code.
For every down-set Lambda of Par_m and every M' in T^{m-1}: brute-force fibre size #{y in T : lambda(y,M') in Lambda}
must equal F_Lambda(lambda(M')) computed as the number of options (in chain order) lying in Lambda,
and must equal formula (5.1): r + (q-1-2l)*N + (l - j0 + 1)[j0 exists]."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/',1)[0])
from p3_slices import partitions_upto, downsets, options, preceq

def lam_of(M, h):
    res = []
    for u in range(1, h+1):
        a = M.count(u); b = M.count(-u)
        if a != b: res.append(abs(a-b))
    return tuple(sorted(res, reverse=True))

def formula51(mu, Lam, q):
    h = (q-1)//2; l = len(mu)
    rem = [tuple(sorted([p for p in (mu[:j] + (mu[j]-1,) + mu[j+1:]) if p > 0], reverse=True)) for j in range(l)]
    r = 0
    for j in range(l):
        if rem[j] in Lam: r = j+1
        else: break
    N = 1 if (l < h and tuple(sorted(mu + (1,), reverse=True)) in Lam) else 0
    add = [tuple(sorted(mu[:j] + (mu[j]+1,) + mu[j+1:], reverse=True)) for j in range(l)]
    j0 = None
    for j in range(l):
        if add[j] in Lam: j0 = j+1; break
    return r + (q-1-2*l)*N + ((l - j0 + 1) if j0 else 0)

def main(q, m):
    h = (q-1)//2
    vals = list(range(1, h+1)) + list(range(-h, 0))
    Pm = partitions_upto(m, h); Pm1 = partitions_upto(m-1, h)
    Ds = downsets(Pm)
    fails1 = fails2 = tests = 0
    for Lam in Ds:
        Lam = set(Lam)
        F = {mu: sum(1 for o in options(mu, q) if o in Lam) for mu in Pm1}
        for mu in Pm1:
            tests += 1
            if F[mu] != formula51(mu, Lam, q): fails2 += 1; print("  (5.1) mismatch", sorted(Lam), mu, F[mu], formula51(mu, Lam, q))
        for Mp in itertools.product(vals, repeat=m-1):
            mu = lam_of(Mp, h)
            fib = sum(1 for y in vals if lam_of((y,)+Mp, h) in Lam)
            tests += 1
            if fib != F[mu]: fails1 += 1; print("  P1 mismatch", sorted(Lam), Mp, mu, fib, F[mu])
    print(f"(q,m)=({q},{m}): {len(Ds)} down-sets, tests={tests}, P1 failures={fails1}, (5.1) failures={fails2}")

if __name__ == '__main__':
    for q, m in [(3,4),(3,6),(9,3),(9,4),(9,5),(27,3),(27,4)]:
        main(q, m)
