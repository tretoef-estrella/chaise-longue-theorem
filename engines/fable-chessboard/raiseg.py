# mission 13, PART C: exact gate of the raise certificate (pure Python over F_3, mod box).
# Parent (2,1)(n+1): letters y_1..y_n, z = index n; j = 0, l = 1, P = 2..n-1.
# Omega := (-1)^n sum_{k odd} e_k(Y) h_{M-k}(-j,-z,l), M = 2q+n-8;  Psi := Omega - z^{q-4} phi_jl - y_j^{q-4} phi_zl,
# phi_ab := y_a^{q-2} e_{n-2}(Y \ b) (the (2,1)(n+1) family, f = n-2).
# Claim: Psi == z^{q-2} y_j^{q-2} e_{n-4}(y \ l)  modulo box + (z^{q-1}) + Mon,  Mon = {#zeros <= #(q-1)-exps + 1} (= N_1(n+1) + (x_Y)).
import itertools, sys
def run(n, q):
    V = n+1; z = n; j = 0; l = 1
    def hD(D):
        out = {}; Ls = [j, z, l]
        for a in range(0, min(D, q-1)+1):
            for b in range(0, min(D-a, q-1)+1):
                c = D-a-b
                if c < 0 or c >= q: continue
                t = [0]*V; t[j] = a; t[z] = b; t[l] = c
                out[tuple(t)] = (-1)**(a+b) % 3
        return out
    def ek(k, vs):
        out = {}
        for S in itertools.combinations(vs, k):
            t = [0]*V
            for i in S: t[i] = 1
            out[tuple(t)] = 1
        return out
    def mul(p1, p2):
        out = {}
        for e1, c1 in p1.items():
            for e2, c2 in p2.items():
                e = tuple(a+b for a, b in zip(e1, e2))
                if max(e) >= q or e[z] >= q-1: continue
                out[e] = (out.get(e, 0)+c1*c2) % 3
        return {k: v for k, v in out.items() if v}
    def add(p, r, s=1):
        out = dict(p)
        for k, v in r.items(): out[k] = (out.get(k, 0)+s*v) % 3
        return {k: v for k, v in out.items() if v}
    def mono(**kw):
        t = [0]*V
        for k, v in kw.items(): t[{'j': j, 'z': z, 'l': l}[k]] = v
        return {tuple(t): 1}
    Y = list(range(V)); y = list(range(n))
    M = 2*q+n-8
    Om = {}
    for k in range(1, V+1, 2): Om = add(Om, mul(hD(M-k), ek(k, Y)))
    phi_jl = mul(mono(j=q-2), ek(n-2, [i for i in Y if i != l]))
    phi_zl = mul(mono(z=q-2), ek(n-2, [i for i in Y if i != l]))
    Om = {e: (c*(-1)**n) % 3 for e, c in Om.items()}   # sign (-1)^M = (-1)^n
    Psi = add(add(Om, mul(mono(z=q-4), phi_jl), -1), mul(mono(j=q-4), phi_zl), -1)
    tgt = mul(mono(z=q-2, j=q-2), ek(n-4, [i for i in y if i != l]))
    def inMon(e): return sum(1 for x in e if x == 0) <= sum(1 for x in e if x == q-1)+1
    red = {e: c for e, c in add(Psi, tgt, -1).items() if not inMon(e)}
    tgt_out = all(not inMon(e) for e in tgt)
    return len(red) == 0, tgt_out, len(Om)
for (n, q) in [(5, 9), (6, 9), (7, 9), (8, 9), (5, 27), (6, 27), (7, 27), (5, 81), (6, 81)]:
    ok, to, sz = run(n, q)
    print("parent (2,1)(%d), q=%d: Psi == z^(q-2) phi^(2)_jl mod Mon+box+(z^(q-1)): %s ; target monomials outside Mon: %s ; |Omega| = %d" % (n+1, q, ok, to, sz), flush=True)
