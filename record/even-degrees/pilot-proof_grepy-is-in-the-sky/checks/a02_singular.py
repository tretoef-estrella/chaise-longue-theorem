# a02_singular.py — pilot. Leg A / R2 and R3 by an independent route: Groebner / standard bases in Singular.
#  mode "ring":   dim_{F_p} of the ideal (psi_J) in F_p[G] = m^(2k+1) - vdim( F_p[t]/(t_i^m - 1, psi_J) )   (global ordering dp)
#  mode "local":  m = q = 2^v, p = 2, coordinates s = t - 1 (local ordering ds):
#                 q^(2k+1) - vdim(B/(psi_J(s)))  and  q^(2k+1) - vdim(B/(L_J)),  L_J the forms of lowest degree
# The generators are written from the definitions of MISSION.md section 1 / R3, by this script; nothing is imported.
import sys, subprocess
from eng import matchings, N_odd

def singular(script):
    out = subprocess.run(["Singular", "-q"], input=script, capture_output=True, text=True).stdout
    return [l.strip() for l in out.strip().splitlines() if l.strip()]

def psi_t(J, m):
    f = []
    for (j, l) in J:
        f.append(f"(t({l})-1)")
        if j != 0:
            f.append("(" + "+".join(f"(t({j})*t({l}))^{a}" for a in range(m)) + ")")
    return "*".join(f)

def run_ring(k, m, p):
    n1 = 2 * k + 1
    Js = matchings(range(n1 + 1))
    gens = [f"t({i})^{m}-1" for i in range(1, n1 + 1)] + [psi_t(J, m) for J in Js]
    script = f"ring R={p},(t(1..{n1})),dp;\nideal I=" + ",\n".join(gens) + ";\nvdim(std(I));\nquit;\n"
    v = int(singular(script)[-1])
    d = m ** n1 - v
    G = N_odd(m - 1, 2 * k + 2)
    print(f"RING k={k} m={m} p={p}: vdim quotient={v}  dim ideal={d}  |Gamma|=N_(m-1)(2k+2)={G}  equal={d == G}", flush=True)

def run_local(k, q):
    n1 = 2 * k + 1
    Js = matchings(range(n1 + 1))
    box = [f"s({i})^{q}" for i in range(1, n1 + 1)]
    true, tang = [], []
    for J in Js:
        a, b = [], []
        for (j, l) in J:
            a.append(f"s({l})"); b.append(f"s({l})")
            if j != 0:
                a.append(f"(s({j})+s({l})+s({j})*s({l}))^{q-1}")
                b.append(f"(s({j})+s({l}))^{q-1}")
        true.append("*".join(a)); tang.append("*".join(b))
    res = []
    for gens in (true, tang):
        script = f"ring R=2,(s(1..{n1})),ds;\nideal I=" + ",\n".join(box + gens) + ";\nvdim(std(I));\nquit;\n"
        res.append(q ** n1 - int(singular(script)[-1]))
    G = N_odd(q - 1, 2 * k + 2)
    print(f"LOCAL k={k} q={q}: dim true ideal={res[0]}  dim ideal of the lowest forms L_J={res[1]}  |Gamma|={G}  all equal={res[0] == res[1] == G}", flush=True)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "ring":
        run_ring(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    else:
        run_local(int(sys.argv[2]), int(sys.argv[3]))
