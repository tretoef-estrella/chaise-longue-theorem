"""Theorem 5.3 in full, for EVERY weak-dominance down-set Lambda of Par_m at a cell (q,m):
  (1) dim V_Lambda (linear algebra, my own tight-pattern generator)  vs  |Z_Lambda| (enumeration over T^m);
  (2) the slice inclusions of Prop. 5.8: every generator of V_{Lambda_i} (on indices 2..m) lies in W_{q-2-i}(V_Lambda),
      i.e. y_1^{j} g  in  V_Lambda + span(monomials with y_1-exponent < j), j = q-2-i;
  (3) negative control: the same with j-1 (should FAIL somewhere, per the paper).
Cells chosen: ones the previous referee did not do."""
import sys, itertools, time
from collections import defaultdict
from boxalg import poly_mul, D_poly, monomials_of_degree, P
import flint
from p2check import partitions_upto, leq, norm

def conj(lam):
    return tuple(sum(1 for x in lam if x>=c) for c in range(1,(lam[0] if lam else 0)+1))

def set_partitions_sizes(items, sizes):
    """all ways to split list items into blocks with the given multiset of sizes (sizes sorted desc);
    blocks with equal sizes are unordered (we return sorted tuples of blocks)."""
    if not sizes:
        yield ()
        return
    s=sizes[0]
    first=items[0]
    # the block containing 'first' can have any size present; to avoid duplicates for equal sizes,
    # we simply generate all labelled choices and dedupe by frozenset of blocks
    seen=set()
    for combo in itertools.combinations(items, s):
        rest=[x for x in items if x not in combo]
        for tail in set_partitions_sizes(rest, sizes[1:]):
            blocks=tuple(sorted((combo,)+tail))
            if blocks not in seen:
                seen.add(blocks); yield blocks

def vandermonde(B, nvars, e):
    f={tuple([0]*nvars):1}
    Bs=sorted(B)
    for i in range(len(Bs)):
        for j in range(i+1,len(Bs)):
            g={}
            ex=[0]*nvars; ex[Bs[j]]=1; g[tuple(ex)]=1
            ex=[0]*nvars; ex[Bs[i]]=1; g[tuple(ex)]=P-1
            f=poly_mul(f,g,e)
    return f

def tight_products(lam, idx, nvars, q, e):
    """all tight-pattern products of lam on index list idx (variable indices 0-based)."""
    m=len(idx); p=(m-sum(lam))//2
    assert (m-sum(lam))%2==0 and p>=0
    cols=list(conj(lam))   # column lengths lambda'_c
    out=[]
    for pairset in itertools.combinations(idx, 2*p):
        rest=[x for x in idx if x not in pairset]
        # perfect matchings of pairset
        def matchs(lst):
            if not lst: yield (); return
            a=lst[0]
            for i in range(1,len(lst)):
                for mm in matchs(lst[1:i]+lst[i+1:]): yield ((a,lst[i]),)+mm
        for M in matchs(list(pairset)):
            DP={tuple([0]*nvars):1}
            for (a,b) in M: DP=poly_mul(DP, D_poly(a,b,q,nvars,e), e)
            for blocks in set_partitions_sizes(rest, sorted(cols, reverse=True)):
                f=DP
                for B in blocks: f=poly_mul(f, vandermonde(B,nvars,e), e)
                if f: out.append(f)
    return out

def residue_partition(M, h):
    cnt=defaultdict(int)
    for v in M: cnt[v]+=1
    parts=[]
    for u in range(1,h+1):
        d=abs(cnt[u]-cnt[-u])
        if d: parts.append(d)
    return norm(parts)

def downsets(Par):
    # enumerate all down-sets via antichains: brute force over subsets for small posets
    n=len(Par); res=[]
    for mask in range(1<<n):
        S=[Par[i] for i in range(n) if mask>>i&1]
        ok=True
        for lam in S:
            for mu in Par:
                if mu not in S and leq(mu,lam): ok=False;break
            if not ok: break
        if ok: res.append(tuple(S))
    return res

def rref_basis_by_degree(gens, nvars, e):
    """returns dict degree -> (cols list, colidx, basis as flint nmod_mat in rref, rank)"""
    degs={}
    for g in gens:
        d={sum(k) for k in g}; assert len(d)==1
        degs.setdefault(d.pop(),[]).append(g)
    top=nvars*(e-1); res={}
    if not degs: return res
    for d in range(min(degs), top+1):
        cols=monomials_of_degree(nvars,e,d); colidx={m:i for i,m in enumerate(cols)}
        rows=[]
        for dg,gl in degs.items():
            if dg>d: continue
            for beta in monomials_of_degree(nvars,e,d-dg):
                for g in gl:
                    r={}
                    for ex,c in g.items():
                        ex2=tuple(x+y for x,y in zip(ex,beta))
                        if max(ex2)>=e: continue
                        r[colidx[ex2]]=c
                    if r: rows.append(r)
        if not rows: continue
        M=flint.nmod_mat(len(rows),len(cols),P)
        for i,r in enumerate(rows):
            for c,v in r.items(): M[i,c]=v
        R,rk=M.rref()
        res[d]=(cols,colidx,R,rk)
    return res

def member(basis_d, cols, colidx, g_vec_cols, extra_low_cols):
    """is vector (dict col->coef) in rowspace(basis) + span(unit vectors of extra_low_cols)?"""
    R,rk=basis_d
    nlow=len(extra_low_cols)
    M=flint.nmod_mat(rk+nlow+1, len(cols), P)
    for i in range(rk):
        for c in range(len(cols)):
            v=R[i,c]
            if v: M[i,c]=v
    for i,c in enumerate(extra_low_cols): M[rk+i,c]=1
    base=M.rank()
    for c,v in g_vec_cols.items(): M[rk+nlow,c]=v
    return M.rank()==base

def run(q,m):
    h=(q-1)//2; e=q-1; nvars=m
    Par=[lam for lam in partitions_upto(m,h) if (sum(lam)-m)%2==0]
    Par1=[lam for lam in partitions_upto(m-1,h) if (sum(lam)-(m-1))%2==0]
    T=list(range(1,h+1))+list(range(-h,0))
    lamM={}
    for M in itertools.product(T,repeat=m): lamM[M]=residue_partition(M,h)
    lamM1={}
    for M in itertools.product(T,repeat=m-1): lamM1[M]=residue_partition(M,h)
    DS=downsets(Par)
    print(f"cell (q,m)=({q},{m}): |Par_m|={len(Par)} down-sets={len(DS)}", flush=True)
    bad=0; ctrl_fail=0; ctrl_tests=0
    for Lam in DS:
        LamS=set(Lam)
        Z=sum(1 for M,l in lamM.items() if l in LamS)
        gens=[]
        for lam in Lam: gens+=tight_products(lam, list(range(m)), nvars, q, e)
        if not Lam: gens=[]
        bases=rref_basis_by_degree(gens,nvars,e)
        dimV=sum(b[3] for b in bases.values())
        # layers: F_Lambda(mu) computed from the FIBRES directly (definition), not from formula (5.1)
        F={}
        for mu in Par1:
            # take any M' with lambda(M')=mu and count y in T with lambda(y,M') in Lambda
            Mp=next(Mm for Mm,l in lamM1.items() if l==mu)
            F[mu]=sum(1 for y in T if lamM[(y,)+Mp] in LamS)
        ok=True; ctrl=False
        for i in range(q-1):
            Lami=[mu for mu in Par1 if F[mu]>i]
            j=q-2-i
            gi=[]
            for mu in Lami: gi+=tight_products(mu, list(range(1,m)), nvars, q, e)
            for g in gi:
                dg=sum(next(iter(g)))
                d=dg+j
                if d not in bases:
                    # V_Lambda has nothing in degree d: g must be zero-dim... then membership requires g*y1^j in low span: impossible unless g=0
                    ok=False; print("  no degree",d,"in V_Lambda for",Lam,"i=",i); continue
                cols,colidx,R,rk=bases[d]
                gv={colidx[tuple([j]+list(ex[1:]))]:c for ex,c in g.items() if ex[0]==0}
                low=[ci for ci,mm in enumerate(cols) if mm[0]<j]
                if not member((R,rk),cols,colidx,gv,low):
                    ok=False; print("  SLICE FAIL",Lam,"i=",i,"mu-gen deg",dg)
                    break
                # negative control on the first generator only, j-1 (one slice tighter)
                if j>=1 and not ctrl:
                    ctrl=True; ctrl_tests+=1
                    if (d-1) in bases:
                        cols2,colidx2,R2,rk2=bases[d-1]
                        gv2={colidx2[tuple([j-1]+list(ex[1:]))]:c for ex,c in g.items() if ex[0]==0}
                        low2=[ci for ci,mm in enumerate(cols2) if mm[0]<j-1]
                        if not member((R2,rk2),cols2,colidx2,gv2,low2): ctrl_fail+=1
                    else: ctrl_fail+=1
            if not ok: break
        flag = "OK" if (dimV>=Z and ok) else "FAIL"
        if dimV!=Z or not ok: bad+=1
        print(f"  Lambda={list(Lam)}: dim V={dimV} |Z|={Z} slices={'ok' if ok else 'FAIL'} {flag}", flush=True)
    print(f"cell ({q},{m}) done: down-sets with a problem: {bad}; negative control (one slice tighter): {ctrl_fail}/{ctrl_tests} tests fail", flush=True)

if __name__=="__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
