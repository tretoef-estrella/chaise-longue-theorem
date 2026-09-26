# sk.py — Fable, Mission 15. Tests STRONG KEY on random unions of pattern sets:
#   for Z = union of Z(m;t) (t random types), P = Sat(Z) = {t : Z(m;t) subset Z}, every i:
#   Sat(Z_{>i}) subset Rules_i(P)  (Rules = L1, L2, L2', L3 + monotone union)   [SK]
#   and the weaker KEY-sat: Z_{>i} subset Z(m-1; Rules_i(P)).
# Usage: python3 -u sk.py Q MMAX TRIALS SEED
import sys, random
q, MMAX, TR, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); CLOSE = len(sys.argv) > 5
sys.argv = ['x', '1', str(q)]
from peelcore import *
random.seed(SEED)
def alltypes(m):
    out = []
    def parts(n, mx):
        if n == 0: yield (); return
        for b in range(min(n, mx), 1, -1):
            for r in parts(n-b, b): yield (b,) + r
    for s_ in range(m//2+1):
        for tot in range(0, m-2*s_+1):
            for beta in parts(tot, tot):
                out.append((s_, beta))
    return out
def minus2(beta):
    out = set(); b = list(beta)
    for x in range(len(b)):
        c = list(b); c[x] -= 2; out.add(tuple(sorted([y for y in c if y >= 2], reverse=True)))
        for y in range(x+1, len(b)):
            c = list(b); c[x] -= 1; c[y] -= 1; out.add(tuple(sorted([z for z in c if z >= 2], reverse=True)))
    if not b: out.add(())
    return out
def Zset(m, t): return frozenset(x for x in types(m) if witness(x, t[0], t[1]))
def rules_all(m, P):
    Pall = {}
    for i in range(q-2, -1, -1):
        Pall[i] = canon(m-1, set(children(m, P, i)) | (set(Pall[i+1]) if i+1 in Pall else set()))
    return Pall
fails_sk = 0; fails_key = 0; tests = 0; global_cl = [0]; pi_fail = [0]
for trial in range(TR):
    m = random.randint(2, MMAX)
    T = alltypes(m); ZT = {t: Zset(m, t) for t in T}
    gens = random.sample(T, random.randint(1, min(3, len(T))))
    if CLOSE:
        G = set(gens); ch = True
        while ch:
            ch = False
            for (s_, beta) in list(G):
                for bs in minus2(beta):
                    t = (s_+1, bs)
                    if 2*t[0]+sum(t[1]) <= m and t not in G: G.add(t); ch = True
        gens_c = sorted(G)
    else: gens_c = gens
    Z = frozenset().union(*[ZT[t] for t in gens_c])
    P = frozenset(t for t in T if ZT[t] <= Z)
    fib = {x: fibre(x, P) for x in types(m-1)}
    Pall = rules_all(m, P)
    T1 = alltypes(m-1); ZT1 = {t: Zset(m-1, t) for t in T1}
    for i in range(q-1):
        A = frozenset(x for x in fib if fib[x] > i)
        if not A: continue
        tests += 1
        B = frozenset(x for x in fib if inZ(x, Pall[i]))
        if not A <= B:
            fails_key += 1
            if fails_key <= 5: print('KEY-sat FAIL m=%d gens=%s i=%d missing=%s' % (m, gens, i, sorted(A-B)[:2]))
        satA = [t for t in T1 if ZT1[t] <= A]
        SA = set(satA)
        def desc_ok(t, SA=SA):
            st = [t]; seen_ = set()
            while st:
                u = st.pop()
                for bs in minus2(u[1]):
                    u2 = (u[0]+1, bs)
                    if 2*u2[0]+sum(u2[1]) <= m-1 and ZT1[u2] and u2 not in seen_:
                        if u2 not in SA: return False
                        seen_.add(u2); st.append(u2)
            return True
        Gmax = [t for t in satA if desc_ok(t)]
        ZG = frozenset().union(*[ZT1[t] for t in Gmax]) if Gmax else frozenset()
        if ZG != A:
            pi_fail[0] += 1
            if pi_fail[0] <= 5: print('PI FAIL m=%d gens=%s i=%d |A|=%d |Z(Gmax)|=%d' % (m, gens, i, len(A), len(ZG)))
        for t in satA:
            for bs in minus2(t[1]):
                t2 = (t[0]+1, bs)
                if 2*t2[0]+sum(t2[1]) <= m-1 and t2 not in SA and ZT1[t2]:
                    global_cl[0] += 1
                    if global_cl[0] <= 5: print('CLOSURE FAIL m=%d gens=%s i=%d t=%s t-2=%s' % (m, gens, i, t, t2))
        miss = [t for t in satA if t not in Pall[i] and ZT1[t]]
        if miss:
            fails_sk += 1
            if fails_sk <= 5: print('SK FAIL m=%d gens=%s i=%d types-not-produced=%s' % (m, gens, i, miss[:3]))
print('q=%d trials=%d tests=%d KEY-sat failures=%d SK failures=%d closure failures=%d PI failures=%d' % (q, TR, tests, fails_key, fails_sk, global_cl[0], pi_fail[0]))
