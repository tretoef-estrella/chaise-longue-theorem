-- INFORME_7 STEP 1.12: are the excess forms of the polynomial-indicator identity in R_2 (z^2 X in K_k+(z^3)) / in L = K'_k + pi_z(M_k : z^2)?
-- X1 = (yj-yl)^(q-1) yj R'_j, X2 = yj^(q-1) yl D, X3 = yl^(q-1) yj D ; j = 1, l = 0.
for kq in {{2,9},{2,27},{3,9}} do (
  k = kq#0; q = kq#1; n = 2*k+1;
  S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1)); z = x_(n-1); xp = apply(toList(0..2*k-1), i -> x_i);
  e = (L,j) -> sum apply(subsets(L, j), s -> product s);
  I = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q);
  Mk = ideal(0_S);
  for j from 1 to k do for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
    C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
    Mk = Mk + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
  Kz = I + Mk + ideal(z^3);
  -- L = K'_k + pi_z(M_k : z^2): K'_k = I^(2k) + (e_{2k}(x')) + M'_k ; pi_z(M_k:z^2) = monomials of M_k with z in C or z in B (z-free part)
  Ip = ideal apply(select(toList(1..2*k), i -> odd i), i -> e(xp,i)) + ideal apply(xp, v -> v^q) + ideal(product xp);
  Mp = ideal(0_S);
  for j from 1 to min(2,k-1) do for A in subsets(2*k, j) do for B in subsets(select(toList(0..2*k-1), i -> not member(i,A)), j) do (
    C = select(toList(0..2*k-1), i -> not member(i,A) and not member(i,B));
    Mp = Mp + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
  Mcol = ideal(0_S);
  for j from 1 to k do for A in subsets(2*k, j) do for B in subsets(select(toList(0..2*k-1), i -> not member(i,A)), j-1) do (
    C = select(toList(0..2*k-1), i -> not member(i,A) and not member(i,B));
    Mcol = Mcol + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
  for j from 1 to k do for A in subsets(2*k, j) do for B in subsets(select(toList(0..2*k-1), i -> not member(i,A)), j) do (
    C = select(toList(0..2*k-1), i -> not member(i,A) and not member(i,B));
    Mcol = Mcol + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
  L = Ip + Mp + Mcol;
  yj = x_1; yl = x_0;
  ee = r -> if r < 0 then 0_S else e(xp, r);
  Rp = sum apply(toList(1..k-1), i -> (i % 3) * yj^(2*i-2) * ee(2*k-2-2*i));
  hcomp = (a,b,d) -> if d < 0 then 0_S else sum apply(toList(0..d), i -> a^i * b^(d-i));
  D = sum apply(toList(1..k-1), i -> ee(2*k-2-2*i) * hcomp(yj^2, yl^2, i-1));
  X1 = (yj-yl)^(q-1) * yj * Rp; X2 = yj^(q-1) * yl * D; X3 = yl^(q-1) * yj * D;
  V = apply(toList(1..2*k-1), i -> x_i); s0 = yj^(q-2) * e(V, 2*k-2);
  << "(k,q)=(" << k << "," << q << ")  dim S'/L = " << degree(L) << endl;
  << "   in L:   X1 " << (X1 % L == 0) << "  X2 " << (X2 % L == 0) << "  X3 " << (X3 % L == 0) << "  X1-X2-X3 " << ((X1-X2-X3) % L == 0) << endl;
  << "   in R_2: X1 " << ((z^2*X1) % Kz == 0) << "  X2 " << ((z^2*X2) % Kz == 0) << "  X3 " << ((z^2*X3) % Kz == 0) << "  X1-X2-X3 " << ((z^2*(X1-X2-X3)) % Kz == 0) << "  s0 " << ((z^2*s0) % Kz == 0) << endl;
);
