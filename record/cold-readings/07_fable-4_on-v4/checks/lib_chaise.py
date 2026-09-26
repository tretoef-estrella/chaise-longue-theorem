"""Shared combinatorics for the cold audit of PAPER_OFICIAL_v4 (own code, written from the paper's definitions).
T = {0,...,q-2}; class of u is u//2; negation is u^1 (u XOR 1).  Partitions are tuples sorted decreasingly."""
from itertools import combinations, product
from functools import lru_cache
from math import factorial
from fractions import Fraction

def partitions_of(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0: yield (); return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions_of(n-k, k): yield (k,)+rest

def Par(m, h):
    """Par_m^{(h)} : |lam| <= m, |lam| = m mod 2, length <= h"""
    out=[]
    for s in range(m%2, m+1, 2):
        for lam in partitions_of(s):
            if len(lam) <= h: out.append(lam)
    return out

def S(lam, t):
    return sum(lam[:t])

def leq(lam, mu):
    """weak dominance lam <= mu : S_t(lam) <= S_t(mu) for all t"""
    L = max(len(lam), len(mu))
    return all(S(lam,t) <= S(mu,t) for t in range(1, L+1))

def downsets(P):
    """all down-sets of the finite poset P (list) under leq"""
    P = list(P)
    below = {x: frozenset(y for y in P if leq(y, x)) for x in P}
    seen = {frozenset()}
    frontier = [frozenset()]
    while frontier:
        new=[]
        for D in frontier:
            for x in P:
                if x not in D and below[x] - {x} <= D:
                    E = D | {x}
                    if E not in seen: seen.add(E); new.append(E)
        frontier = new
    return sorted(seen, key=lambda D:(len(D), sorted(D)))

def is_downset(D, P):
    D=set(D)
    return all((y in D) for x in D for y in P if leq(y,x))

def sort_part(parts):
    return tuple(sorted((p for p in parts if p>0), reverse=True))

def residue_partition(M, h):
    cnt = [[0,0] for _ in range(h)]
    for u in M: cnt[u//2][u%2]+=1
    return sort_part(abs(a-b) for a,b in cnt)

def nu(M,h):
    cnt = [[0,0] for _ in range(h)]
    for u in M: cnt[u//2][u%2]+=1
    return sum(min(a,b) for a,b in cnt)

def options(mu, h, q):
    """the q-1 options of a tail of shape mu, in chain order (positions 1..q-1)"""
    l = len(mu); L=q-1
    rem = [sort_part(mu[:j]+(mu[j]-1,)+mu[j+1:]) for j in range(l)]
    add = [sort_part(mu[:j]+(mu[j]+1,)+mu[j+1:]) for j in range(l)]
    mid = [sort_part(mu+(1,))]*(L-2*l)
    return rem + mid + list(reversed(add))

def F_Lambda(mu, Lam, h, q):
    return sum(1 for o in options(mu,h,q) if o in Lam)

def layers(Lam, m, h, q):
    P1 = Par(m-1, h)
    return [frozenset(mu for mu in P1 if F_Lambda(mu,Lam,h,q) > i) for i in range(q-1)]

def count_Z(Lam, m, h):
    """|Z_Lambda| by brute force over T^m"""
    q1 = 2*h
    Lam=set(Lam); c=0
    for M in product(range(q1), repeat=m):
        if residue_partition(M,h) in Lam: c+=1
    return c

def count_shape_formula(lam, m, h):
    """#{M in T^m : lambda(M)=lam} via exponential generating functions (independent of the fibre route)."""
    # class with imbalance d contributes sum_b x^{2b+d}/(b!(b+d)!) * 2 (which sign is majority) if d>0, and I_0 if d=0
    from collections import Counter
    l=len(lam)
    if l>h: return 0
    N=m
    def I(d):
        return [Fraction(1, factorial(b)*factorial(b+d)) if (n-d)%2==0 and n>=d and (b:=(n-d)//2)>=0 else Fraction(0) for n in range(N+1)]
    def mul(A,B):
        C=[Fraction(0)]*(N+1)
        for i,a in enumerate(A):
            if a==0: continue
            for j,b in enumerate(B):
                if i+j<=N: C[i+j]+=a*b
        return C
    # choose which classes get which parts: ordered assignment of distinct classes to the parts, divided by symmetries of equal parts
    cnt=Counter(lam)
    ways=Fraction(1)
    rem=h
    for part,mult in cnt.items():
        # choose mult classes out of rem
        from math import comb
        ways*=comb(rem,mult); rem-=mult
    ways*=2**l
    poly=[Fraction(1)]+[Fraction(0)]*N
    for part in lam: poly=mul(poly,I(part))
    for _ in range(h-l): poly=mul(poly,I(0))
    return int(ways*poly[N]*factorial(N))

def Qk(k,q):
    h=(q-1)//2; N=2*k+2
    I0=[Fraction(1,factorial(b)**2) if n%2==0 and (b:=n//2)>=0 else Fraction(0) for n in range(N+1)]
    poly=[Fraction(1)]+[Fraction(0)]*N
    for _ in range(h):
        C=[Fraction(0)]*(N+1)
        for i,a in enumerate(poly):
            for j,b in enumerate(I0):
                if i+j<=N: C[i+j]+=a*b
        poly=C
    return int(poly[N]*factorial(N))

def matchings(idx):
    idx=list(idx)
    if not idx: yield []; return
    a=idx[0]
    for b in idx[1:]:
        rest=[x for x in idx if x not in (a,b)]
        for M in matchings(rest): yield [(a,b)]+M

def set_partitions_with_sizes(I, sizes):
    """all ways to split list I into labelled blocks of the given sizes (order of blocks = order of sizes)"""
    I=list(I)
    if not sizes:
        if not I: yield []
        return
    s=sizes[0]
    for B in combinations(I, s):
        rest=[x for x in I if x not in B]
        for R in set_partitions_with_sizes(rest, sizes[1:]): yield [B]+R

def conjugate(lam):
    if not lam: return ()
    return tuple(sum(1 for p in lam if p>=c) for c in range(1, lam[0]+1))

def tight_patterns(lam, I):
    """yield (pairs, blocks) : p=(|I|-|lam|)/2 disjoint pairs, blocks of sizes lam'_c covering the rest"""
    I=list(I); p=(len(I)-sum(lam))
    assert p%2==0 and p>=0
    p//=2
    cols=conjugate(lam)
    for pairs in choose_disjoint_pairs(I,p):
        used={x for pr in pairs for x in pr}
        rest=[x for x in I if x not in used]
        for blocks in set_partitions_with_sizes(rest, list(cols)):
            yield pairs, blocks

def choose_disjoint_pairs(I,p):
    I=list(I)
    if p==0: yield []; return
    # choose the pair containing the smallest element that IS paired: iterate over which elements are paired
    for paired in combinations(I, 2*p):
        for M in matchings(paired): yield M

# ---- polynomials as dict {exp tuple: int coeff} ----
def poly_mul(A,B,box=None):
    C={}
    for ea,ca in A.items():
        for eb,cb in B.items():
            e=tuple(x+y for x,y in zip(ea,eb))
            if box is not None and any(x>=box for x in e): continue
            C[e]=C.get(e,0)+ca*cb
    return {e:c for e,c in C.items() if c!=0}

def var(i,m):
    e=[0]*m; e[i]=1; return {tuple(e):1}
def const(c,m): return {tuple([0]*m):c} if c!=0 else {}
def poly_add(A,B):
    C=dict(A)
    for e,c in B.items(): C[e]=C.get(e,0)+c
    return {e:c for e,c in C.items() if c!=0}
def poly_scale(A,c): return {e:c*v for e,v in A.items()} if c!=0 else {}
def poly_pow(A,n,m):
    R=const(1,m)
    for _ in range(n): R=poly_mul(R,A)
    return R

def D_poly(a,b,q,m):
    """D(y_a,y_b) = sum_{u=0}^{q-2} (-1)^u y_a^u y_b^{q-2-u}, indices a,b are 0-based variable indices"""
    P={}
    for u in range(q-1):
        e=[0]*m; e[a]+=u; e[b]+=q-2-u
        P[tuple(e)]=P.get(tuple(e),0)+(-1)**u
    return P

def Delta_poly(B,m):
    B=sorted(B); R=const(1,m)
    for i in range(len(B)):
        for j in range(i+1,len(B)):
            R=poly_mul(R, poly_add(var(B[j],m), poly_scale(var(B[i],m),-1)))
    return R

def pattern_product(pairs, blocks, q, m):
    R=const(1,m)
    for a,b in pairs:
        a,b=min(a,b),max(a,b)
        R=poly_mul(R,D_poly(a,b,q,m))
    for B in blocks: R=poly_mul(R,Delta_poly(B,m))
    return R

def V_generators(Lam, m, q, idx=None):
    """generators of V_Lambda on variables idx (default 0..m-1), as polys in m variables"""
    if idx is None: idx=list(range(m))
    gens=[]
    for lam in Lam:
        for pairs,blocks in tight_patterns(lam, idx):
            g=pattern_product(pairs,blocks,q,m)
            if g: gens.append(g)
    return gens
