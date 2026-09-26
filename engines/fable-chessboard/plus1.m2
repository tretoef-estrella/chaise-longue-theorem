-- INFORME_7 STEP 2: the explicit +1-row ideals. Even: Q_k = (e_odd(x'), box, e_{2k}(x'), x_C x_{A'}^(q-1): A' u B u C = x', |A'|=j-1, |B|=j, 1<=j<=k) in S_{2k};
-- odd: Q'_k = (e_odd(x'), box, e_{2k-1}(x'), x_C x_{A'}^(q-1): |A'|=j-1, |B|=j, 1<=j<=min(2,k-1)) in S_{2k-1}. Colengths vs fibre sizes.
for kq in {{2,9},{2,27},{3,9}} do (
  k = kq#0; q = kq#1;
  for par in {0,1} do (
    n = if par == 0 then 2*k else 2*k-1;
    S = ZZ/3[x_0..x_(n-1)]; vs = toList(x_0..x_(n-1));
    e = (L,j) -> sum apply(subsets(L, j), s -> product s);
    Q = ideal apply(select(toList(1..n), i -> odd i), i -> e(vs,i)) + ideal apply(vs, v -> v^q) + ideal(product vs);
    jmax = if par == 0 then k else min(2,k-1);
    for j from 1 to jmax do for Ap in subsets(n, j-1) do for B in subsets(select(toList(0..n-1), i -> not member(i,Ap)), j) do (
      C = select(toList(0..n-1), i -> not member(i,Ap) and not member(i,B));
      Q = Q + ideal((product apply(C, i -> x_i)) * (product apply(Ap, i -> x_i^(q-1)))));
    << "(k,q)=(" << k << "," << q << ") " << (if par == 0 then "even Q_k  " else "odd  Q'_k ") << " colength = " << degree Q << endl;
  );
);
