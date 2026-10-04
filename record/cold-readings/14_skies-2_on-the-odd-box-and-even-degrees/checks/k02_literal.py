# k02_literal.py -- Grepy Skies 2. The literal ideal of [DS] in F_p[G], for EVEN m:
#   dim_{F_p} (psi_J : J) F_p[G]  =  m^{2k+1} - vdim F_p[t]/(t_i^m - 1, psi_J)   against |Gamma| = N_{m-1}(2k+2).
# Two independent routes: (S) Groebner basis in Singular; (L) my own linear algebra (span of the translates
# g*psi_J, g in G) with python-flint, in the small cells.
# control that can fail: one matching removed (the dimension must drop below |Gamma|).
# usage: python3 k02_literal.py "k,m,p k,m,p ..." [nolinalg]
import sys, subprocess, itertools, time, os
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import matchings, Nr
from flint import nmod_mat

def psi_strings(k, m):
    out = []
    for J in matchings(list(range(2 * k + 2))):
        fac = []
        for (j, kk) in J:
            fac.append("(t%d-1)" % kk)
            if j != 0:
                fac.append("(" + "+".join("(t%d*t%d)^%d" % (j, kk, e) for e in range(m)) + ")")
        out.append("*".join(fac))
    return out

def singular_dim(k, m, p, gens):
    n1 = 2 * k + 1
    vs = ",".join("t%d" % i for i in range(1, n1 + 1))
    code = "ring R=%d,(%s),dp;\n" % (p, vs)
    code += "ideal B=" + ",".join("t%d^%d-1" % (i, m) for i in range(1, n1 + 1)) + ";\n"
    code += "qring Q=std(B);\n"
    code += "ideal I=" + ",\n".join(gens) + ";\n"
    code += "ideal G=std(I);\nprint(vdim(G));\nquit;\n"
    fn = "checks/_k02_tmp.sing"
    open(fn, "w").write(code)
    res = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True)
    lines = [l for l in res.stdout.strip().splitlines() if l.strip()]
    return m ** n1 - int(lines[-1])

def linalg_dim(k, m, p, Jlist):
    """span over F_p of g*psi_J (g in G = (Z/m)^{2k+1}); psi_J as an element of the group ring."""
    n1 = 2 * k + 1
    def idx(e):
        v = 0
        for x in e: v = v * m + (x % m)
        return v
    size = m ** n1
    rows = []
    for J in Jlist:
        # psi_J = prod (t_k - 1) * prod_{pairs not containing 0} sum_e (t_j t_k)^e
        poly = {tuple([0] * n1): 1}
        for (j, kk) in J:
            new = {}
            for e, c in poly.items():
                e1 = list(e); e1[kk - 1] = (e1[kk - 1] + 1) % m
                new[tuple(e1)] = (new.get(tuple(e1), 0) + c) % p
                new[e] = (new.get(e, 0) - c) % p
            poly = {a: b for a, b in new.items() if b}
            if j != 0:
                new = {}
                for e, c in poly.items():
                    for s in range(m):
                        e1 = list(e); e1[j - 1] = (e1[j - 1] + s) % m; e1[kk - 1] = (e1[kk - 1] + s) % m
                        new[tuple(e1)] = (new.get(tuple(e1), 0) + c) % p
                poly = {a: b for a, b in new.items() if b}
        rows.append(poly)
    # translates: the ideal is the span of all g*psi_J
    ent = []
    nrows = 0
    for poly in rows:
        for g in itertools.product(range(m), repeat=n1):
            row = [0] * size
            for e, c in poly.items():
                row[idx([a + b for a, b in zip(e, g)])] = c
            ent.extend(row); nrows += 1
    return nmod_mat(nrows, size, ent, p).rank()

cells = [tuple(int(x) for x in c.split(',')) for c in sys.argv[1].split()]
do_lin = not (len(sys.argv) > 2 and sys.argv[2] == 'nolinalg')
for (k, m, p) in cells:
    t0 = time.time()
    G = Nr(m - 1, 2 * k + 2)
    gens = psi_strings(k, m)
    dS = singular_dim(k, m, p, gens)
    tS = time.time() - t0
    line = "(k,m,p)=(%d,%d,%d): |Gamma| = N_%d(%d) = %d ; Singular: dim (psi_J) = %d [%s, %.1fs]" % (
        k, m, p, m - 1, 2 * k + 2, G, dS, "EQUAL" if dS == G else "DIFFERENT", tS)
    Jl = list(matchings(list(range(2 * k + 2))))
    if do_lin and len(Jl) * m ** (2 * (2 * k + 1)) <= 40_000_000:
        t1 = time.time()
        dL = linalg_dim(k, m, p, Jl)
        line += " ; my linear algebra: %d [%s, %.1fs]" % (dL, "EQUAL" if dL == G else "DIFFERENT", time.time() - t1)
    # control: one matching removed (the first and the last)
    ctl = []
    for omit in (0, len(gens) - 1):
        ctl.append(singular_dim(k, m, p, gens[:omit] + gens[omit + 1:]))
    line += " ; control, one matching removed: %s (all < |Gamma|: %s)" % (ctl, all(c < G for c in ctl))
    print(line, flush=True)
if os.path.exists("checks/_k02_tmp.sing"): os.remove("checks/_k02_tmp.sing")
