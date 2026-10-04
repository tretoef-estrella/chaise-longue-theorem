# chkE5.py -- brute force for piece E5 (q_quartic_assembly.md). Grepy Chats, 2 Oct 2026.
# The rank of the ideal I = (psi_J) of F_p[G], G = (Z/m)^(2k+1), i.e. rank_{F_p}(A), against Q^e_k(m):
#   m = 4, k = 1, 2, over p = 2 (the prime of H(4,k)), 3, 5, 7, 1000003;
#   m = 6, 8, k = 1, over the primes that divide m and over primes that do not.
# The functions are those of chkE2.py (lines 1-136), executed here unchanged.
import sys, time
T0 = time.time()
src = open('chkE2.py').read().split('\ngood = {')[0]
exec(src)
# The matrices of chkE2.py are int32, which is right for small primes; for p = 1000003 the products of the
# elimination reach 10^12 and overflow (first run: «rank» 64, 1024, 216, 512 = full, impossible since
# rank_F(A) <= rank_Q(A)). Here the same function with int64.
def ideal_rank(m, k, p, sign=-1, drop=None):
    d = 2*k + 1; cols = list(itertools.product(range(m), repeat=d)); idx = {e: i for i, e in enumerate(cols)}
    Js = list(matchings_list(list(range(2*k + 2))))
    if drop is not None: Js = Js[:drop] + Js[drop+1:]
    A = np.zeros((len(Js) * len(cols), len(cols)), dtype=np.int64); r = 0
    for J in Js:
        P = psi(J, m, d, p, sign)
        for nu in cols:
            for e, c in P.items(): A[r, idx[tuple((x + y) % m for x, y in zip(e, nu))]] = c
            r += 1
    return rank_mod(A, p)
checks = bad = 0
def chk(name, ok, extra=''):
    global checks, bad
    checks += 1; bad += (not ok)
    print(('ok   ' if ok else 'FAIL ') + name + (' | ' + extra if extra else ''), flush=True)
for (m, k, primes) in [(4, 1, [2, 3, 5, 7, 1000003]), (4, 2, [2, 3, 5, 7, 1000003]),
                       (6, 1, [2, 3, 5, 7, 1000003]), (8, 1, [2, 3, 5, 1000003])]:
    Q = Qe_explicit(k, m)
    assert Q == Qe_rec(k, m)
    for p in primes:
        r = ideal_rank(m, k, p)
        kind = 'p | m' if m % p == 0 else 'p does not divide m'
        chk(f"rank over F_{p} of A(m={m}, k={k}) = Qe = {Q} ({kind})", r == Q, f"rank {r}")
    print(f"   t={time.time()-T0:.1f}s", flush=True)
# the free rank: 4^(2k+1) - Qe
chk("4^3 - Qe_1(4) = 45", 4**3 - Qe_explicit(1, 4) == 45)
chk("4^5 - Qe_2(4) = 883", 4**5 - Qe_explicit(2, 4) == 883)
# controls (each can fail): one matching removed; phi_m replaced by phi_(m-1)
fired = 0; ncon = 0
for (m, k, p) in [(4, 1, 2), (4, 1, 3), (6, 1, 5), (8, 1, 3)]:
    r = ideal_rank(m, k, p, drop=0); ncon += 1; f = (r != Qe_explicit(k, m)); fired += f
    print(('CONTROL fires   ' if f else 'CONTROL SILENT  ') + f"one matching removed, m={m} k={k} p={p}: rank {r} vs {Qe_explicit(k, m)}", flush=True)
def psi_wrong(J, m, d, p):
    def t(a):
        e = [0]*d; e[a-1] = 1; return tuple(e)
    P = {(0,)*d: 1}
    for (a, b) in J:
        P = polymul(P, {t(b): 1, (0,)*d: (-1) % p}, m, p)
        if a > 0:
            phi = {}
            for s in range(m - 1):                      # phi_(m-1) instead of phi_m
                e = [0]*d; e[a-1] = s; e[b-1] = s; phi[tuple(e)] = 1
            P = polymul(P, phi, m, p)
    return P
_psi = psi
for (m, k, p) in [(4, 1, 2), (4, 1, 5), (4, 2, 2)]:
    psi = lambda J, m_, d, p_, sign=-1: psi_wrong(J, m_, d, p_)
    r = ideal_rank(m, k, p); psi = _psi; ncon += 1; f = (r != Qe_explicit(k, m)); fired += f
    print(('CONTROL fires   ' if f else 'CONTROL SILENT  ') + f"phi_(m-1) in place of phi_m, m={m} k={k} p={p}: rank {r} vs {Qe_explicit(k, m)}", flush=True)
print(f"CHECKS {checks}  FAILURES {bad}")
print(f"CONTROLS {ncon}  FIRED {fired}")
print(f"time {time.time()-T0:.1f}s")
print("FIN-OK")
