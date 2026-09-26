-- INFORME_7 STEP 2 (A): lemma (O1_4) at the allowed cell (4,3): is z'*x_c*x_A^(q-1) (|A|=|B|=3, C={c,z'}) in K'_4 = I^(8) + (e_8) + M'_4 ?
q = 3; k = 4; n = 2*k;
S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1)); zp = x_(n-1);
e = (L,j) -> sum apply(subsets(L, j), s -> product s);
Ip = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(product vs);
Mp = ideal(0_S);
for j from 1 to min(2,k-1) do for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
  C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
  Mp = Mp + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
Kp = Ip + Mp;
<< "K'_4 at q=3 built, numgens " << numgens Kp << endl;
<< "dim S_8/K'_4 = " << degree Kp << endl;
-- j=3 monomial: A={0,1,2}, B={3,4,5}, C={6,7} (x_7 = z')
m3 = x_6 * zp * x_0^(q-1) * x_1^(q-1) * x_2^(q-1);
<< "(O1_4) at q=3: z'*x_6*x_0^2 x_1^2 x_2^2 in K'_4: " << (m3 % Kp == 0) << endl;
-- also: is the row-1 inclusion R'_1 ⊇ K_3 true at (4,3)? i.e. all M^(3)({0..6}) monomials times z' in K'_4
allok = true;
for A in subsets(7, 3) do for B in subsets(select(toList(0..6), i -> not member(i,A)), 3) do (
  C = select(toList(0..6), i -> not member(i,A) and not member(i,B));
  mm = zp * (product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)));
  if mm % Kp != 0 then allok = false);
<< "all z'*M^(3)({0..6}) monomials in K'_4 at q=3: " << allok << endl;
