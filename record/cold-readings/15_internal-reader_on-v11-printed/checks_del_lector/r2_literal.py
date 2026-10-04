# R2 (Grepy Tinta): the literal ring of [DS]. Own code.
# F_p[G], G=(Z/m)^{n1}, n1=2k+1, basis t^nu, index = sum nu_i * m^(i-1) (variable t_i has stride m^(i-1)).
import itertools, sys, time
import numpy as np
def matchings(S):
    S=list(S)
    if not S: yield []; return
    a=S[0]
    for i in range(1,len(S)):
        b=S[i]; rest=S[1:i]+S[i+1:]
        for M in matchings(rest): yield [(a,b)]+M
def psi(J,m,n1,sign=-1):
    # psi_J = prod_{i=0..k} (t_{k_i} + sign) * prod_{i>=1} phi(t_{j_i} t_{k_i}); returns integer array of shape (m,)*n1 (axis i-1 <-> t_i)
    A=np.zeros((m,)*n1,dtype=np.int64); A[(0,)*n1]=1
    def mul_lin(A,ax):      # multiply by (t_ax + sign)
        return np.roll(A,1,axis=ax)+sign*A
    def mul_phi(A,ax1,ax2): # multiply by sum_c (t_ax1 t_ax2)^c
        B=np.zeros_like(A)
        for c in range(m): B+=np.roll(np.roll(A,c,axis=ax1),c,axis=ax2)
        return B
    for (j,kk) in J:
        A=mul_lin(A,kk-1)
        if j!=0: A=mul_phi(A,j-1,kk-1)
    return A
def flat(A,n1):  # index = sum nu_i m^(i-1): axis 0 (t_1) least significant
    return np.transpose(A,axes=list(range(n1-1,-1,-1))).reshape(-1)
def ideal_dim_p2(gens,m,n1):
    L=m**n1
    idx=np.arange(L)
    masks=[]
    for i in range(n1):
        s=m**i; dig=(idx//s)%m
        lo=int.from_bytes(np.packbits((dig<m-1).astype(np.uint8),bitorder='little').tobytes(),'little')
        hi=int.from_bytes(np.packbits((dig==m-1).astype(np.uint8),bitorder='little').tobytes(),'little')
        masks.append((s,lo,hi))
    basis={}
    def insert(v):
        while v:
            h=v.bit_length()-1
            b=basis.get(h)
            if b is None: basis[h]=v; return True
            v^=b
        return False
    queue=[]
    for g in gens:
        v=int.from_bytes(np.packbits((g%2).astype(np.uint8),bitorder='little').tobytes(),'little')
        if insert(v): queue.append(v)
    while queue:
        v=queue.pop()
        for (s,lo,hi) in masks:
            w=((v&lo)<<s)|((v&hi)>>((m-1)*s))
            if insert(w): queue.append(w)
    return len(basis)
def ideal_dim_odd(gens,m,n1,p):
    L=m**n1; idx=np.arange(L)
    perms=[]
    for i in range(n1):
        s=m**i; dig=(idx//s)%m
        tgt=np.where(dig<m-1, idx+s, idx-(m-1)*s)
        perms.append(tgt)
    piv=[]; rows=[]; pivset={}
    def insert(v):
        v=v%p
        while True:
            nz=np.flatnonzero(v)
            if nz.size==0: return None
            h=int(nz[0])
            j=pivset.get(h)
            if j is None:
                inv=pow(int(v[h]),-1,p); v=(v*inv)%p
                pivset[h]=len(rows); rows.append(v); return v
            v=(v-int(v[h])*rows[j])%p
    queue=[]
    for g in gens:
        r=insert(g.astype(np.int64))
        if r is not None: queue.append(r)
    while queue:
        v=queue.pop()
        for tgt in perms:
            w=np.zeros(L,dtype=np.int64); w[tgt]=v
            r=insert(w)
            if r is not None: queue.append(r)
    return len(rows)
def cell(k,m,p,drop=None,sign=-1):
    n1=2*k+1
    Js=list(matchings(range(n1+1)))
    if drop is not None: Js=[J for i,J in enumerate(Js) if i!=drop]
    gens=[flat(psi(J,m,n1,sign),n1) for J in Js]
    return ideal_dim_p2(gens,m,n1) if p==2 else ideal_dim_odd(gens,m,n1,p)
def run(tag,cells):
    for c in cells:
        t=time.time(); d=cell(*c[:3],**(c[3] if len(c)>3 else {}))
        print(tag,c,'dim =',d,'(%.1fs)'%(time.time()-t)); sys.stdout.flush()
print('== P2.5 odd published cells =='); run('P2.5',[(1,3,3),(1,9,3),(2,3,3),(1,5,5)])
print('== P2.1 even m, p | m ==')
run('P2.1',[(1,4,2),(1,6,2),(1,6,3),(1,8,2),(1,10,2),(1,10,5),(1,12,2),(1,12,3),(1,14,2),(1,14,7),(1,16,2),(2,4,2),(2,6,2),(2,6,3),(2,8,2),(3,4,2)])
print('== P2.2 p not dividing m =='); run('P2.2',[(1,4,3),(1,6,5),(2,4,3)])
print('== P2.3 control: one matching removed =='); run('P2.3',[(1,4,2,{'drop':0}),(1,6,3,{'drop':0}),(2,4,2,{'drop':0}),(1,6,2,{'drop':0})])
print('== P2.4 control: sign in tau_J =='); run('P2.4',[(1,6,3,{'sign':1}),(1,10,5,{'sign':1})])
