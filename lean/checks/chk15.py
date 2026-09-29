import itertools, math
from collections import Counter
def shape(xi,eta):
    X=Counter(xi); Y=Counter(eta); vals=set(X)|set(Y)
    lp=sorted([X[u]-Y[u] for u in vals if X[u]>Y[u]],reverse=True)
    lm=sorted([Y[u]-X[u] for u in vals if Y[u]>X[u]],reverse=True)
    return tuple(lp),tuple(lm)
def Nbal(a,q): return sum(1 for xi in itertools.product(range(q),repeat=a) for eta in itertools.product(range(q),repeat=a) if Counter(xi)==Counter(eta))
def Nbal_formula(a,q):
    tot=0
    for c in itertools.product(range(a+1),repeat=q):
        if sum(c)==a: tot+=(math.factorial(a)//math.prod(math.factorial(x) for x in c))**2
    return tot
def Nph(a,q): return sum(1 for xi in itertools.product(range(q),repeat=a+1) for eta in itertools.product(range(q),repeat=a) if not (Counter(eta)-Counter(xi)))
print('Nbal(a,3)',[Nbal(a,3) for a in range(1,5)],[Nbal_formula(a,3) for a in range(1,6)])
print('Nbal(2,q)',[Nbal(2,q) for q in (3,5,7,9,11)])
print('Nph=Nbal(a+1)',all(Nph(a,q)==Nbal(a+1,q) for q in (3,5,7) for a in range(0,3)), [Nph(a,3) for a in range(4)])
bad=0;n=0
for q in (3,5):
  for al in range(0,4):
    for be in range(0,4):
      for xi in itertools.product(range(q),repeat=al):
        for eta in itertools.product(range(q),repeat=be):
          lp,lm=shape(xi,eta); n+=1
          ok = sum(lp)-sum(lm)==al-be and sum(lp)+sum(lm)<=al+be and len(lp)+len(lm)<=q
          ok = ok and ((lp,lm)==((),()))==(Counter(xi)==Counter(eta))
          if al==be+1: ok = ok and ((lp,lm)==((1,),()))==(not (Counter(eta)-Counter(xi)))
          if not ok: bad+=1
print('shape properties',n,'points, failures',bad)
