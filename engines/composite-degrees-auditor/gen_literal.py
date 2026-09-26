# Generates a Singular script for the LITERAL ring of [DS]: F_p[t_1..t_{n+1}]/(t_i^m-1) modulo psi_J (J in K).
import sys, itertools
def matchings(s):
    if not s: yield []; return
    a=s[0]
    for i in range(1,len(s)):
        b=s[i]; rest=s[1:i]+s[i+1:]
        for M in matchings(rest): yield [(a,b)]+M
def script(m,p,k,drop=()):
    n=2*k; V=[f"t{i}" for i in range(1,n+2)]
    L=[f"ring r = {p},({','.join(V)}),dp;", "option(redSB);"]
    L.append(f"proc phi(poly u) {{ poly s=0; int i; for(i=0;i<{m};i++){{ s=s+u^i; }} return(s); }}")
    gens=[f"t{i}^{m}-1" for i in range(1,n+2)]
    Js=list(matchings(list(range(n+2))))
    for idx,J in enumerate(Js):
        if idx in drop: continue
        J=sorted(J)
        tau="*".join(f"(t{b}-1)" for (a,b) in J)
        ph="*".join(f"phi(t{a}*t{b})" for (a,b) in J if a!=0)
        gens.append(tau+("*"+ph if ph else ""))
    L.append("ideal I = "+",\n".join(gens)+";")
    L.append("int v = vdim(std(I));")
    L.append(f'print("m={m} p={p} k={k} drop={list(drop)} quotient="+string(v)+" dim_ideal="+string({m}^{n+1}-v));')
    L.append("kill r;")
    return "\n".join(L)
if __name__=="__main__":
    m,p,k=map(int,sys.argv[1:4]); drop=tuple(map(int,sys.argv[4].split(","))) if len(sys.argv)>4 else ()
    print(script(m,p,k,drop)); print("quit;")
