-- INFORME_7 STEP 2: odd generic row R'_2 = pi_{z'}(K'_k : z'^2) vs L' + (s'_0 family), at (2,9), (2,27), (3,9).
for kq in {{2,9},{2,27},{3,9}} do (
  k = kq#0; q = kq#1; n = 2*k;
  S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1)); zp = x_(n-1); xp = apply(toList(0..n-2), i -> x_i);
  e = (L,j) -> sum apply(subsets(L, j), s -> product s);
  Ip = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(product vs);
  Mp = ideal(0_S);
  for j from 1 to min(2,k-1) do for A in subsets(n, j) do for B in subsets(select(toList(0..n-1), i -> not member(i,A)), j) do (
    C = select(toList(0..n-1), i -> not member(i,A) and not member(i,B));
    Mp = Mp + ideal((product apply(C, i -> x_i)) * (product apply(A, i -> x_i^(q-1)))));
  Kp = Ip + Mp;
  Kz = Kp + ideal(zp^3);
  C2 = Kz : zp^2;
  T = ZZ/3[x_0..x_(n-2)];
  pz = map(T, S, append(apply(toList(0..n-2), i -> x_i), 0_T));
  R2 = pz C2;
  -- sum of colons L' = pi(I^(2k) : z') + pi(M'_k : z'^2) + (e_{2k-1}(x')) (INFORME_5 §2.12), computed directly
  Lp = pz((Ip + ideal(zp^3)) : zp) + pz((Mp + ideal(zp^3)) : zp^2);
  -- s'_0 family: y_j^(q-2) e_{2k-3}(x' \ y_l), all j != l, in T
  use T; xt = toList(x_0..x_(n-2));
  fam = ideal(0_T);
  for l from 0 to n-2 do for j from 0 to n-2 do if j != l then (
    V = select(xt, v -> v != x_l);
    fam = fam + ideal(x_j^(q-2) * e(V, 2*k-3)));
  << "(k,q)=(" << k << "," << q << ")  colength R'_2 = " << degree R2 << " ; L' = " << degree Lp << " ; L'+fam = " << degree(Lp+fam)
     << " ; fam subset R'_2: " << isSubset(fam, R2) << " ; R'_2 subset L'+fam: " << isSubset(R2, Lp+fam) << endl;
  G = mingens (R2 + Lp + fam);  -- generators of R'_2 not in L'+fam: degrees
  extra = select(numcols G, i -> (G_(0,i) % (Lp+fam)) != 0);
  << "   mingens of R'_2 beyond L'+fam, degrees: " << tally apply(extra, i -> (degree G_(0,i))#0) << endl;
  for i in extra do if (degree G_(0,i))#0 <= 2*k-1 then << "     " << G_(0,i) << endl;
);
