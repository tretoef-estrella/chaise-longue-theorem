-- Gate for the mechanism at k=3, q=9: colon of K3+(z^3) by x1^(q-2) in 7 variables; low-degree structure; target of (G-a_3)
q = 9;
S = ZZ/3[x0,x1,x2,x3,x4,x5,z]; vs = {x0,x1,x2,x3,x4,x5,z}; n = 7;
box = ideal apply(vs, v -> v^q);
e = j -> sum apply(subsets(vs, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + box;
-- M_3 = sum_{j=1}^{3} M^(j): x_C x_A^(q-1), A,B,C partition of {0..6}, |A|=|B|=j
Mk = ideal(0_S);
for j from 1 to 3 do (
  for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
    C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
    Mk = Mk + ideal((product apply(C, i -> vs#i)) * (product apply(A, i -> (vs#i)^(q-1))));
  );
);
K3 = I7 + Mk;
<< "K3 built, numgens " << numgens K3 << endl;
tgt = z^2*x0^2*x1^(q-2)*(sum apply(subsets({x1,x2,x3,x4,x5},2), s -> product s));
K3z = K3 + ideal(z^3);
<< "(G-a_3) at q=9: " << (tgt % K3z == 0) << endl;
C = K3z : x1^(q-2);
MC = mingens C;
<< "colon mingens degrees: " << tally apply(numcols MC, i -> (degree MC_(0,i))#0) << endl;
low = select(numcols MC, i -> (degree MC_(0,i))#0 <= 8);
Clow = ideal apply(low, i -> MC_(0,i));
t4 = z^2*x0^2*(sum apply(subsets({x1,x2,x3,x4,x5},2), s -> product s));
<< "target/x1^(q-2) in colon: " << (t4 % C == 0) << "   in the low-degree (<=8) part alone: " << (t4 % Clow == 0) << endl;
lowfree = select(low, i -> (degree(x1, MC_(0,i))) == 0);
<< "number of low generators, and x1-free ones: " << #low << " " << #lowfree << endl;
for i in low do if (degree MC_(0,i))#0 <= 4 then << "   " << MC_(0,i) << endl;
