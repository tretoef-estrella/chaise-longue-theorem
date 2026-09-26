-- INFORME_7 STEP 2: q = 81 gates in <= 5 variables (allowed). (i) X1-X2-X3 in L at (2,81), 4 variables; (ii) z*tau_{jl}+z^2*s0 in I^(5)+(z^3) at (2,81), 5 variables.
q = 81; k = 2;
S4 = ZZ/3[x_0..x_3]; xp = toList(x_0..x_3);
e = (L,j) -> sum apply(subsets(L, j), s -> product s);
Ip = ideal apply(select(toList(1..4), i -> odd i), i -> e(xp,i)) + ideal apply(xp, v -> v^q) + ideal(product xp);
Mp = ideal(0_S4);
for j from 1 to min(2,k-1) do for A in subsets(4, j) do for B in subsets(select(toList(0..3), i -> not member(i,A)), j) do (
  C = select(toList(0..3), i -> not member(i,A) and not member(i,B));
  Mp = Mp + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
Mcol = ideal(0_S4);
for j from 1 to k do for A in subsets(4, j) do for B in subsets(select(toList(0..3), i -> not member(i,A)), j-1) do (
  C = select(toList(0..3), i -> not member(i,A) and not member(i,B));
  Mcol = Mcol + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
for j from 1 to k do for A in subsets(4, j) do for B in subsets(select(toList(0..3), i -> not member(i,A)), j) do (
  C = select(toList(0..3), i -> not member(i,A) and not member(i,B));
  Mcol = Mcol + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
L = Ip + Mp + Mcol;
yj = x_1; yl = x_0;
ee = r -> if r < 0 then 0_S4 else e(xp, r);
Rp = sum apply(toList(1..k-1), i -> (i % 3) * yj^(2*i-2) * ee(2*k-2-2*i));
hcomp = (a,b,d) -> if d < 0 then 0_S4 else sum apply(toList(0..d), i -> a^i * b^(d-i));
D = sum apply(toList(1..k-1), i -> ee(2*k-2-2*i) * hcomp(yj^2, yl^2, i-1));
X1 = (yj-yl)^(q-1) * yj * Rp; X2 = yj^(q-1) * yl * D; X3 = yl^(q-1) * yj * D;
<< "(2,81) dim S_4/L = " << degree L << "  ;  X1-X2-X3 in L: " << ((X1-X2-X3) % L == 0) << "  (X1 alone: " << (X1 % L == 0) << ")" << endl;
S5 = ZZ/3[x_0..x_4]; vs = toList(x_0..x_4); z = x_4;
I5 = ideal apply(select(toList(1..5), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(z^3);
tl = x_1^(q-1) * x_2 * x_3; s0 = x_1^(q-2) * e({x_1,x_2,x_3}, 2);
<< "(2,81) z*tau_{jl} + z^2*s0 in I^(5)+(z^3): " << ((z*tl + z^2*s0) % I5 == 0) << endl;
