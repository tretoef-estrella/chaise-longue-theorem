# R8 (Grepy Tinta): Pfaffian identities behind Proposition 8.10, over Z. Variable 0 is y_1.
import sys, itertools, time
SRC=open('checks/r3_thm811_v3.py').read().split('# ---------- main ----------')[0]
t0=time.time()
def env(r):
    sys.argv=['x',str(r),'1','2']; g={}; exec(SRC,g); return g
def run(r):
    g=env(r); h=(r-1)//2
    pmul,padd,mono,one,Dpoly,Dminus,vander,pfaff,Eset,pf_bordered=[g[k] for k in ['pmul','padd','mono','one','Dpoly','Dminus','vander','pfaff','Eset','pf_bordered']]
    def pf_cols(m,Nset,cols):     # general bordered Pfaffian: cols = list of dicts {index: poly}
        Nl=sorted(Nset); n=len(Nl); s=len(cols)
        if (n+s)%2: return {}
        A={}
        for a in range(n):
            for b in range(a+1,n): A[(a,b)]=Dminus(m,Nl[a],Nl[b])
            for kk in range(s): A[(a,n+kk)]=cols[kk][Nl[a]]
        if n+s==0: return one(m)
        return pfaff(A)(tuple(range(n+s)))
    def deg0(P): return max((e[0] for e in P),default=-1)
    def coef0(P,j): return {(0,)+e[1:]:c for e,c in P.items() if e[0]==j}
    def pm_equal(P,Q):
        return P==Q or P=={k:-v for k,v in Q.items()}
    # (M), delta=1
    for l in range(0,h):
        for t in ([0,1,2] if r==5 else [0,1]):
            n=l+1+2*t; m=n+1
            if m>6: continue
            B0=list(range(1,m)); Ep=list(range(l))
            A=pf_bordered(m,[0]+B0,Ep)
            colsE=[{b:mono(m,b,e) for b in B0} for e in Ep]
            Bp=pf_cols(m,B0,colsE+[{b:Dpoly(m,0,b) for b in B0}])
            Bm=pf_cols(m,B0,colsE+[{b:Dminus(m,0,b) for b in B0}])
            target=pf_bordered(m,B0,Eset(l))
            yA=pmul(mono(m,0,1),A) if A else {}
            out=[]
            for th in (1,-1):
                f=padd(yA,Bp,th)
                d=deg0(f); top=coef0(f,l) if d==l else None
                out.append((th,d,top is not None and pm_equal(top,target)))
            good=[o for o in out if o[1]==l and o[2]]
            print('(M,d=1) r=%d l=%d t=%d: target Pf_{E_l}(B_0) nonzero: %s ; D^- part nonzero: %s ; (theta, y1-degree, top=+-G): %s  -> %s'%(r,l,t,bool(target),bool(Bm),out,'OK' if (len(good)>=1) else ('vacuous (G=0)' if not target and all(o[1]<=l for o in out[:1]) else 'FAIL'))); sys.stdout.flush()
    # (Z), delta=0
    for l in range(1,h+1):
        m=l+1; B1=list(range(1,m))
        A=pf_bordered(m,[0]+B1,Eset(l)); d=deg0(A)
        print('(Z,d=0) r=%d l=%d: y1-degree=%d (claimed %d) ; top = +-Delta(B_1): %s'%(r,l,d,r-l-1,pm_equal(coef0(A,d),vander(m,B1))))
    # (R), delta=1, mu_rho=1
    for l in range(1,h+1):
        for t in (0,1):
            n=l+1+2*t; m=n+1
            if m>6: continue
            B0=list(range(1,m))
            A=pf_bordered(m,[0]+B0,Eset(l-1)); target=pf_bordered(m,B0,Eset(l)); d=deg0(A)
            ok=(d==r-l and pm_equal(coef0(A,d),target)) if target else (d<r-l or not coef0(A,r-l))
            print('(R,d=1,mu_rho=1) r=%d l=%d t=%d: y1-degree=%d (claimed %d) ; G nonzero: %s ; top = +-Pf_{E_l}(B_0): %s'%(r,l,t,d,r-l,bool(target),ok)); sys.stdout.flush()
    # (Z), delta=1 : (F6) with D
    for l in range(0,min(h,3)+1):
        m=l+2; S=list(range(1,m)); rho=len(S); f={}
        for c,b in enumerate(S,1):
            term=pmul(vander(m,[x for x in S if x!=b]),Dpoly(m,0,b))
            f=padd(f,term,(-1)**(rho+c))
        d=deg0(f)
        print('(Z,d=1) r=%d l=%d: y1-degree=%d (claimed %d) ; top = +-Delta(S): %s'%(r,l,d,r-1-l,pm_equal(coef0(f,d),vander(m,S))))
for r in (3,5,7): run(r)
print('time %.1fs'%(time.time()-t0))
