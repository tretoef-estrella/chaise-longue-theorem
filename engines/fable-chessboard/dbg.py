import sys
sys.argv=['x','1','81']
from peelcore import *
def alltypes(m):
    out = []
    def parts(n, mx):
        if n == 0: yield (); return
        for b in range(min(n, mx), 1, -1):
            for r in parts(n-b, b): yield (b,) + r
    for s_ in range(m//2+1):
        for tot in range(0, m-2*s_+1):
            for beta in parts(tot, tot): out.append((s_, beta))
    return out
def Zset(m, t): return frozenset(x for x in types(m) if witness(x, t[0], t[1]))
m=5; T=alltypes(m); ZT={t:Zset(m,t) for t in T}
Z=ZT[(1,(3,))]
P=frozenset(t for t in T if ZT[t]<=Z)
print(sorted(P))
x=((1,1),(1,1),(1,0))
print('in types?', x in types(5), 'witness 2 pairs', witness(x,2,()), 'in Z', x in Z, witness(x,1,(3,)))
