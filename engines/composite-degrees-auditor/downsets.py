# Gate D (own code): Theorem BP on EVERY down-set of Par_q(alpha,beta); ideals in Singular, points by enumeration.
# Also Gate P: chain, options-in-Par, P1 (brute force over tails), P2 (all comparable pairs) at many cells.
import itertools, sys, subprocess, collections
def parts(n, maxpart=None):
    if maxpart is None: maxpart=n
    if n==0: yield (); return
    for k in range(min(n,maxpart),0,-1):
        for r in parts(n-k,k): yield (k,)+r
def S(l,t): return sum(l[:t])
def wdom(l,m):  # l <= m weak dominance
    L=max(len(l),len(m))+1
    return all(S(l,t)<=S(m,t) for t in range(1,L+1))
def Par(q,al,be):
    out=[]
    for sp in range(0,al+1):
        sm=sp-(al-be)
        if sm<0 or sm>be: continue
        for lp in parts(sp):
            for lm in parts(sm):
                if len(lp)+len(lm)<=q and sp+sm<=al+be: out.append((lp,lm))
    return out
def le(A,B): return wdom(A[0],B[0]) and wdom(A[1],B[1])
def srt(l): return tuple(sorted([x for x in l if x>0],reverse=True))
def options(mu,q):
    mp,mm=mu; lp,lm=len(mp),len(mm); ops=[]
    for p in range(1,q+1):
        if p<=lm: x=list(mm); x[p-1]-=1; ops.append((mp,srt(x)))
        elif p<=q-lp: ops.append((srt(list(mp)+[1]),mm))
        else:
            j=q+1-p; x=list(mp); x[j-1]+=1; ops.append((srt(x),mm))
    return ops
def shape(xi,eta):
    X=collections.Counter(xi); Y=collections.Counter(eta)
    Rp=[X[u]-Y[u] for u in X if X[u]>Y[u]]; Rm=[Y[u]-X[u] for u in Y if Y[u]>X[u]]
    return (srt(Rp),srt(Rm))
def gateP(al,be,q):
    tails=Par(q,al-1,be); big=set(Par(q,al,be)); bad=0; npairs=0
    for mu in tails:
        ops=options(mu,q)
        if not all(o in big for o in ops): bad+=1
        if not all(le(ops[i],ops[i+1]) for i in range(q-1)): bad+=1
    for mu in tails:
        for nu in tails:
            if mu!=nu and le(mu,nu):
                npairs+=1
                a,b=options(mu,q),options(nu,q)
                if not all(le(a[i],b[i]) for i in range(q)): bad+=1
    return len(tails),npairs,bad
def gateP1(al,be,q):
    T=range(q); bad=0; n=0
    for xi in itertools.product(T,repeat=al-1):
        for eta in itertools.product(T,repeat=be):
            n+=1
            got=collections.Counter(shape(xi+(u,),eta) for u in T)
            exp=collections.Counter(options(shape(xi,eta),q))
            if got!=exp: bad+=1
    return n,bad
def downsets(P):
    # all down-sets (antichain-generated) of poset P
    P=list(P); res=set()
    idx={x:i for i,x in enumerate(P)}
    below={x:frozenset(y for y in P if le(y,x)) for x in P}
    # enumerate down-sets by recursion over elements sorted by size
    order=sorted(P,key=lambda x:(sum(x[0])+sum(x[1]),x))
    def rec(i,cur):
        if i==len(order): res.add(frozenset(cur)); return
        x=order[i]
        rec(i+1,cur)
        if below[x]-{x} <= cur: rec(i+1,cur|{x})
    rec(0,frozenset()); return res
def conj(l):
    return [sum(1 for x in l if x>c) for c in range(l[0])] if l else []
def patterns(lam,A,B):
    lp,lm=lam; npair=len(A)-sum(lp)
    cp,cm=conj(list(lp)),conj(list(lm))
    for Ap in itertools.combinations(A,npair):
        for Bp in itertools.combinations(B,npair):
            for perm in itertools.permutations(Bp):
                restA=[a for a in A if a not in Ap]; restB=[b for b in B if b not in Bp]
                for blA in setparts(restA,cp):
                    for blB in setparts(restB,cm):
                        yield list(zip(Ap,perm)),blA,blB
def setparts(rest,sizes):
    if not sizes: 
        if not rest: yield []
        return
    s=sizes[0]
    for c in itertools.combinations(rest,s):
        r2=[x for x in rest if x not in c]
        for tail in setparts(r2,sizes[1:]): yield [c]+tail
def vand(vs):
    return "*".join(f"({vs[j]}-{vs[i]})" for i in range(len(vs)) for j in range(i+1,len(vs))) or "1"
def gateD(al,be,q,p):
    A=list(range(1,al+1)); B=list(range(1,be+1))
    P=Par(q,al,be); Ds=downsets(P)
    # point counts by shape
    cnt=collections.Counter()
    for xi in itertools.product(range(q),repeat=al):
        for eta in itertools.product(range(q),repeat=be): cnt[shape(xi,eta)]+=1
    X=[f"x{i}" for i in A]; Z=[f"z{j}" for j in B]
    lines=[f"ring r = {p},({','.join(X+Z) if X+Z else 'w'}),dp;"]
    gen={}
    for lam in P:
        g=[]
        for pr,blA,blB in patterns(lam,A,B):
            t=[f"(x{i}-z{j})^{q-1}" for i,j in pr]+[vand([f'x{i}' for i in c]) for c in blA]+[vand([f'z{j}' for j in c]) for c in blB]
            g.append("*".join(t) if t else "1")
        gen[lam]=g
    out=[]
    for k,D in enumerate(sorted(Ds,key=lambda s:(len(s),sorted(s)))):
        z=sum(cnt[l] for l in D)
        gs=[x for l in D for x in gen[l]]
        box=[f"{v}^{q}" for v in X+Z]
        lines.append(f"ideal I{k}="+",".join(box+(gs if gs else ['0']))+";")
        lines.append(f'print("D{k} Z={z} dim="+string({q**(al+be)}-vdim(std(I{k}))));')
    lines.append("quit;")
    open(f"D_{al}_{be}_{q}.sing","w").write("\n".join(lines))
    res=subprocess.run(["Singular","-q",f"D_{al}_{be}_{q}.sing"],capture_output=True,text=True).stdout
    fails=0; eq=0; n=0
    for line in res.splitlines():
        if line.startswith("D"):
            z=int(line.split("Z=")[1].split()[0]); d=int(line.split("dim=")[1]); n+=1
            if d<z: fails+=1
            if d==z: eq+=1
    return len(Ds),n,fails,eq
if __name__=="__main__":
    mode=sys.argv[1]
    for tok in sys.argv[2:]:
        c=tuple(map(int,tok.split(":")))
        if mode=="P": print("P",c,"tails,pairs,bad=",gateP(*c[:3]),flush=True)
        if mode=="P1": print("P1",c,"tails,bad=",gateP1(*c[:3]),flush=True)
        if mode=="D": print("D",c,"downsets,measured,fails(dim<Z),equalities=",gateD(*c),flush=True)
