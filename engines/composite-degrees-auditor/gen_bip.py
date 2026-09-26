# Gate B: bipartite root ideals I_a (balanced) and I'_a (phantom), own engine (Singular).
import sys, itertools
def script(a,q,p,phantom):
    na = a+1 if phantom else a
    X=[f"x{i}" for i in range(1,na+1)]; Z=[f"z{j}" for j in range(1,a+1)]
    L=[f"ring r = {p},({','.join(X+Z)}),dp;"]
    gens=[f"{v}^{q}" for v in X+Z]
    if phantom:
        for i0 in range(1,na+1):
            rest=[i for i in range(1,na+1) if i!=i0]
            for s in itertools.permutations(range(1,a+1)):
                gens.append("*".join(f"(x{i}-z{j})^{q-1}" for i,j in zip(rest,s)) or "1")
    else:
        for s in itertools.permutations(range(1,a+1)):
            gens.append("*".join(f"(x{i}-z{j})^{q-1}" for i,j in zip(range(1,a+1),s)) or "1")
    L.append("ideal I="+",".join(gens)+";")
    L.append("int v=vdim(std(I));")
    tot=q**(na+a)
    L.append(f'print("{"phantom" if phantom else "balanced"} a={a} q={q} char={p}: dim ideal="+string({tot}-v));')
    L.append("kill r;")
    return "\n".join(L)
if __name__=="__main__":
    out=[]
    for tok in sys.argv[1:]:
        kind,a,q,p=tok.split(":"); out.append(script(int(a),int(q),int(p),kind=="P"))
    out.append("quit;"); print("\n".join(out))
