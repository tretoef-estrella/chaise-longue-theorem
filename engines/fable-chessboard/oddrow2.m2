-- INFORME_7 STEP 2: (3,9) odd generic row: what is left beyond L' + (s'_0 family) + (q-free quartic, quintic)?
k = 3; q = 9; n = 6;
S = ZZ/3[x_0..x_5]; vs = toList(x_0..x_5); zp = x_5;
e = (L,j) -> sum apply(subsets(L, j), s -> product s);
Ip = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(product vs);
Mp = ideal(0_S);
for j from 1 to 2 do for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
  C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
  Mp = Mp + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
Kz = Ip + Mp + ideal(zp^3);
C2 = Kz : zp^2;
T = ZZ/3[x_0..x_4];
pz = map(T, S, append(apply(toList(0..4), i -> x_i), 0_T));
R2 = pz C2;
Lp = pz((Ip + ideal(zp^3)) : zp) + pz((Mp + ideal(zp^3)) : zp^2);
use T; xt = toList(x_0..x_4);
fam = ideal(0_T);
for l from 0 to 4 do for j from 0 to 4 do if j != l then fam = fam + ideal(x_j^(q-2) * e(select(xt, v -> v != x_l), 3));
qfree = ideal(0_T);
G = mingens R2;
for i from 0 to numcols G - 1 do if (degree G_(0,i))#0 <= 5 and (G_(0,i) % (Lp+fam)) != 0 then qfree = qfree + ideal(G_(0,i));
<< "q-free part: " << numgens qfree << " generators, degrees " << apply(numgens qfree, i -> (degree qfree_i)#0) << endl;
B = Lp + fam + qfree;
<< "colengths: R'_2 = " << degree R2 << " ; L'+fam+qfree = " << degree B << endl;
G2 = mingens (R2 + B); extra = select(numcols G2, i -> (G2_(0,i) % B) != 0);
<< "remaining mingens beyond B: " << #extra << " ; degrees " << apply(extra, i -> (degree G2_(0,i))#0) << endl;
for i in extra do << "   " << G2_(0,i) << endl;
-- candidates (INFORME_5 §2.12 forms), all j,b,c
cand1 = ideal apply(flatten apply(xt, b -> apply(xt, j -> if b != j then b^3 * j^(q-2) else 0_T)), f -> f);
h2 = (a,b) -> a^2 + a*b + b^2;
cand2 = ideal(0_T);
for j from 0 to 4 do for b from 0 to 4 do for c from b+1 to 4 do if j != b and j != c then cand2 = cand2 + ideal(x_j^(q-2) * (x_b*x_c*(x_b+x_c) + x_j*h2(x_b,x_c)));
<< "cand1 (y_b^3 y_j^(q-2)) subset R'_2: " << isSubset(cand1, R2) << " ; B+cand1 colength " << degree(B+cand1) << endl;
<< "cand2 (y_j^(q-2)[y_by_c(y_b+y_c)+y_j h_2(y_b,y_c)]) subset R'_2: " << isSubset(cand2, R2) << " ; B+cand2 colength " << degree(B+cand2) << endl;
<< "B + cand1 + cand2 colength " << degree(B+cand1+cand2) << " (target 380)" << endl;
