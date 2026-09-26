-- INFORME_7 STEP 2 (C): odd Lemma-H gate: z'*tau'_{jl} + z'^2*s'_0 in I^(2k) + (z'^3)?  x' = x_0..x_{2k-2}, z' = x_{2k-1}, l=0, j=1
for kq in {{2,9},{2,27},{3,9}} do (
  k = kq#0; q = kq#1; n = 2*k;
  S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1)); zp = x_(n-1);
  e = (L,j) -> sum apply(subsets(L, j), s -> product s);
  I = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(zp^3);
  P = apply(toList(2..2*k-2), i -> x_i); V = apply(toList(1..2*k-2), i -> x_i);
  tl = x_1^(q-1) * product P; s0 = x_1^(q-2) * e(V, 2*k-3);
  << "(k,q)=(" << k << "," << q << ")  z'*tau' + z'^2*s'0 in I^(2k)+(z'^3): " << ((zp*tl + zp^2*s0) % I == 0)
    << " ; z'^2*s'0 alone: " << ((zp^2*s0) % I == 0) << " ; z'*tau' alone: " << ((zp*tl) % I == 0) << endl;
);
