# INFORME_7 tool: exact F_q arithmetic (q = 3^v, v <= 4) with integer encoding, and the point sets of the campaign.
# Elements are ints 0..q-1 encoding tuples (c_0,..,c_{v-1}) base 3 (c_0 least significant); field = F_3[t]/(irr).
import itertools
IRR = {3:[0], 9:[1,0], 27:[1,2,0], 81:[2,0,0,1]}   # t^v = -(sum irr[i] t^i)
class Fq:
    def __init__(self, q):
        v = {3:1,9:2,27:3,81:4}[q]; self.q=q; self.v=v; poly = IRR[q]
        def tup(n): return tuple((n//3**i)%3 for i in range(v))
        def num(t): return sum(c*3**i for i,c in enumerate(t))
        def mul_t(a,b):
            res=[0]*(2*v-1)
            for i,x in enumerate(a):
                if x==0: continue
                for j,y in enumerate(b): res[i+j]=(res[i+j]+x*y)%3
            for k in range(2*v-2, v-1, -1):
                c=res[k]
                if c:
                    res[k]=0
                    for i in range(v): res[k-v+i]=(res[k-v+i]-c*poly[i])%3
            return tuple(res[:v])
        T=[tup(n) for n in range(q)]
        self.add=[[num(tuple((x+y)%3 for x,y in zip(T[a],T[b]))) for b in range(q)] for a in range(q)]
        self.mul=[[num(mul_t(T[a],T[b])) for b in range(q)] for a in range(q)]
        self.neg=[num(tuple((-x)%3 for x in T[a])) for a in range(q)]
        self.one=1; self.zero=0
        self.inv=[0]*q
        for a in range(1,q):
            for b in range(1,q):
                if self.mul[a][b]==1: self.inv[a]=b
        # sanity: field
        for a in range(1,q): assert self.mul[a][self.inv[a]]==1
        self.m1=self.neg[1]
    def pw(self,a,n):
        r=1
        for _ in range(n): r=self.mul[r][a]
        return r
    def s(self,*xs):
        r=0
        for x in xs: r=self.add[r][x]
        return r
    def p(self,*xs):
        r=1
        for x in xs: r=self.mul[r][x]
        return r
    def esym(self,vals,j):
        # elementary symmetric e_j(vals)
        E=[1]+[0]*len(vals)
        for x in vals:
            for d in range(len(vals),0,-1): E[d]=self.add[E[d]][self.mul[E[d-1]][x]]
        return E[j] if j<=len(vals) else 0
    def closed_sets(self,n):
        # all vectors in F_q^n whose multiset is closed under negation (Z_n)
        out=[]
        for x in itertools.product(range(self.q),repeat=n):
            cnt={}
            for a in x: cnt[a]=cnt.get(a,0)+1
            if all(cnt.get(self.neg[a],0)==c for a,c in cnt.items()): out.append(x)
        return out
    def W0(self,k):
        # W_0 = {y in F_q^{2k} : y u {0,1} closed}
        return [y for y in itertools.product(range(self.q),repeat=2*k) if self.is_closed(list(y)+[0,1])]
    def Wv(self,k,v):
        return [y for y in itertools.product(range(self.q),repeat=2*k) if self.is_closed(list(y)+[v,1])]
    def is_closed(self,xs):
        cnt={}
        for a in xs: cnt[a]=cnt.get(a,0)+1
        return all(cnt.get(self.neg[a],0)==c for a,c in cnt.items())
if __name__=="__main__":
    for q in (9,27):
        F=Fq(q)
        for k in (2,3):
            if q==27 and k==3: continue
            W=F.W0(k); print("q=%d k=%d |W_0|=%d"%(q,k,len(W)))
