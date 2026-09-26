import itertools, sys
from collections import Counter
from comb7 import BPar, bdom, shape, srt
from bip import polymul, lin, powp, idealdim
def conj(l):
    return tuple(sum(1 for x in l if x>c) for c in range(l[0])) if l else ()
def setpartitions_into_blocks(elems, sizes):
    # ordered blocks with given sizes (columns); yields list of tuples
    if not sizes: 
        if not elems: yield []
        return
    s=sizes[0]
    for comb in itertools.combinations(elems,s):
        rest=[e for e in elems if e not in comb]
        for r in setpartitions_into_blocks(rest,sizes[1:]): yield [comb]+r
def vand(vars_,nv,box,p):
    g={tuple([0]*nv):1}
    for i in range(len(vars_)):
        for j in range(i+1,len(vars_)):
            e1=[0]*nv;e1[vars_[j]]=1;e2=[0]*nv;e2[vars_[i]]=1
            g=polymul(g,{tuple(e1):1,tuple(e2):p-1},box,p)
    return g
def gens_of(lam,al,be,q,p):
    lp,lm=lam; nv=al+be; npairs=al-sum(lp)
    A=list(range(al)); B=list(range(al,al+be)); out=[]
    for As in itertools.combinations(A,npairs):
        for Bs in itertools.permutations(B,npairs):
            g={tuple([0]*nv):1}
            for i,l in zip(As,Bs): g=polymul(g,powp(lin(nv,i,l,p),q-1,q,p,nv),q,p)
            if not g: continue
            restA=[a for a in A if a not in As]; restB=[b for b in B if b not in Bs]
            for bp in setpartitions_into_blocks(restA,list(conj(lp))):
                for bm in setpartitions_into_blocks(restB,list(conj(lm))):
                    h=g
                    for blk in bp+bm: h=polymul(h,vand(list(blk),nv,q,p),q,p)
                    if h: out.append(h)
    return out
def downsets(P):
    P=list(P); res=[]
    for mask in range(1<<len(P)):
        S=[P[i] for i in range(len(P)) if mask>>i&1]
        if all(x in S for s in S for x in P if bdom(x,s)): res.append(S)
    return res
def Zcount(L,al,be,q):
    Ls=set(L); c=0
    for pt in itertools.product(range(q),repeat=al+be):
        if shape(pt[:al],pt[al:]) in Ls: c+=1
    return c
q=int(sys.argv[1]); al=int(sys.argv[2]); be=int(sys.argv[3]); p=int(sys.argv[4])
P=BPar(q,al,be); D=downsets(P); print("shapes",len(P),"downsets",len(D),flush=True)
bad=0; eq=0
for L in D:
    if not L: continue
    gens=[g for lam in L for g in gens_of(lam,al,be,q,p)]
    d=idealdim(gens,al+be,q,p); z=Zcount(L,al,be,q)
    if d<z: bad+=1; print("FAIL",L,d,z)
    if d==z: eq+=1
print("q al be p",q,al,be,p,"bad",bad,"eq",eq,"of",len(D)-1)
