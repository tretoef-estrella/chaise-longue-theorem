# verify the two function identities on V'_1 = perm(-1,0,c,-c) over F_q, q = 9, 27, 81 (F_q = F_3[t]/(irreducible))
import itertools
def make_field(q):
    # F_3^v via polynomial basis; use Conway-like irreducibles
    irr = {9:[1,0,1] , 27:[1,2,0,1], 81:[2,0,0,1,1]}  # coefficients low->high excluding leading? use explicit: x^2+1 ; x^3+2x+1 ; x^4+x^3+2  (check irreducible below)
    v = {9:2,27:3,81:4}[q]
    poly = {9:[1,0], 27:[1,2,0], 81:[2,0,0,1]}[q]  # x^v = -(poly[0] + poly[1] x + ...) i.e. x^v + ... reduction: x^v = -sum poly[i] x^i
    # elements as tuples of length v over Z3
    els = list(itertools.product(range(3), repeat=v))
    def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
    def neg(a): return tuple((-x)%3 for x in a)
    def mul(a,b):
        res = [0]*(2*v-1)
        for i,x in enumerate(a):
            if x==0: continue
            for j,y in enumerate(b):
                res[i+j] = (res[i+j] + x*y)%3
        for k in range(2*v-2, v-1, -1):
            c = res[k]
            if c:
                res[k]=0
                for i in range(v):
                    res[k-v+i] = (res[k-v+i] - c*poly[i])%3
        return tuple(res[:v])
    zero = tuple([0]*v); one = tuple([1]+[0]*(v-1))
    # check field: every nonzero has inverse (x^(q-1)=1)
    def pw(a,n):
        r = one
        for _ in range(n): r = mul(r,a)
        return r
    for a in els:
        if a!=zero and pw(a,q-1)!=one: raise Exception("not a field for q=%d"%q)
    return els, add, neg, mul, zero, one, pw
for q in [9,27,81]:
    els, add, neg, mul, zero, one, pw = make_field(q)
    m1 = neg(one)
    def s(*xs):
        r = zero
        for x in xs: r = add(r,x)
        return r
    pts = set()
    for c in els:
        for p in itertools.permutations([m1, zero, c, neg(c)]):
            pts.add(p)
    okE3 = okE5 = okE4 = True
    for (x0,x1,x2,x3) in pts:
        eps2 = s(mul(x0,x1),mul(x0,x2),mul(x0,x3),mul(x1,x2),mul(x1,x3),mul(x2,x3))
        # E3: x1^(q-2) eps2 == x1^3 + x1 eps2 - x1
        lhs = mul(pw(x1,q-2), eps2); rhs = s(pw(x1,3), mul(x1,eps2), neg(x1))
        if lhs!=rhs: okE3=False
        # E5: x3^3 x1^(q-2) == x1x3 + x1x3(x3+1)(x1+x3) + x1x3(x1+x3) sum_{j=0}^{q-4} x1^j
        lhs = mul(pw(x3,3), pw(x1,q-2))
        S = zero
        for j in range(q-3): S = add(S, pw(x1,j))
        rhs = s(mul(x1,x3), mul(mul(mul(x1,x3),add(x3,one)),add(x1,x3)), mul(mul(mul(x1,x3),add(x1,x3)),S))
        if lhs!=rhs: okE5=False
    print("q=%d |V'_1|=%d  identity E3 holds: %s   identity E5 holds: %s" % (q, len(pts), okE3, okE5))

# third identity (for E4): x1^(q-2) (x0^2+x2^2+x3^2) == x1^(q-2) + x1 + x1^3 + x1*eps2 on V'_1
for q in [9,27,81]:
    els, add, neg, mul, zero, one, pw = make_field(q)
    m1 = neg(one)
    def s(*xs):
        r = zero
        for x in xs: r = add(r,x)
        return r
    pts = set()
    for c in els:
        for p in itertools.permutations([m1, zero, c, neg(c)]):
            pts.add(p)
    ok = True
    for (x0,x1,x2,x3) in pts:
        eps2 = s(mul(x0,x1),mul(x0,x2),mul(x0,x3),mul(x1,x2),mul(x1,x3),mul(x2,x3))
        lhs = mul(pw(x1,q-2), s(mul(x0,x0),mul(x2,x2),mul(x3,x3)))
        rhs = s(pw(x1,q-2), x1, pw(x1,3), mul(x1,eps2))
        if lhs!=rhs: ok=False
    print("q=%d identity E4' (x1^(q-2) p2'' = x1^(q-2)+x1+x1^3+x1 eps2 on V'_1): %s" % (q, ok))
