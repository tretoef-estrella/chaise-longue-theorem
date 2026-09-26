-- INFORME_7 STEP 1.5: ideal-side gate of the descent: z*t_l + z^2*s0 in I^(2k+1) + (z^3)  (Lemma H conclusion, WITHOUT M_k)
-- t_l = x1^(q-1) * prod_{P} x,  s0 = x1^(q-2) e_{2k-2}(x1..x_{2k-1}),  l = 0, j = 1, P = {2..2k-1}
for kq in {{2,9},{2,27},{3,9}} do (
  k = kq#0; q = kq#1; n = 2*k+1;
  S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1)); z = x_(n-1);
  e = (L,j) -> sum apply(subsets(L, j), s -> product s);
  I = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(z^3);
  P = apply(toList(2..2*k-1), i -> x_i); V = apply(toList(1..2*k-1), i -> x_i);
  tl = x_1^(q-1) * product P; s0 = x_1^(q-2) * e(V, 2*k-2);
  << "(k,q)=(" << k << "," << q << ")  z*t_l + z^2*s0 in I^(2k+1)+(z^3): " << ((z*tl + z^2*s0) % I == 0)
    << " ; z^2*s0 alone: " << ((z^2*s0) % I == 0) << " ; z*t_l alone: " << ((z*tl) % I == 0) << endl;
);
