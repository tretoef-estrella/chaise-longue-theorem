-- INFORME_9 STEP 1 run 3: which top forms tau in Ntilde_{m-1}(n) suffice for s = y_j^(q-2) e_c(y\y_l) ?
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
cells = {{6,2},{6,1},{5,1}};
for cell in cells do (
  nn = cell#0; m = cell#1; n = nn - 1; c = n - m - 1; d = q + n - m - 2;
  << "=== cell (" << nn << "," << m << ") n=" << n << " c=" << c << " d=" << d << endl << flush;
  S = ZZ/3[x_1..x_nn]; vs = gens S; z = x_nn; yv = take(vs, n);
  I1 = ideal apply(select(toList(1..nn), j -> odd j), j -> esym(vs, j)) + ideal apply(vs, v -> v^q);
  T = ZZ/3[x_1..x_n]; pz = map(T, S, append(gens T, 0_T)); yy = gens T;
  ss = (yy#0)^(q-2) * esym(drop(yy, {1,1}), c);
  yj = yv#0; yl = yv#1; P = drop(yv, {0,1});
  rowOf = G -> pz((I1 + z*G + ideal(z^3)) : z^2);
  tst = (name, G) -> ( R := rowOf G; << "  tau-class " << name << " : s in row? " << ((ss % R) == 0) << "  (colength " << degree R << ")" << endl << flush; );
  -- known part alone (G = 0)
  tst("none", ideal(0_S));
  -- single monomials y_j^(q-1) x_C, |C| = c, by whether l in C
  Cn := subsets(P, c); if #Cn > 0 then tst("y_j^(q-1) x_C, C subset P, |C|=c (one C)", ideal(yj^(q-1) * product(Cn#0)));
  tst("all y_j^(q-1) x_C, C subset P, |C|=c", ideal apply(Cn, C -> yj^(q-1) * product C));
  Cl := subsets(P, c-1); tst("all y_j^(q-1) y_l x_C', C' subset P, |C'|=c-1", ideal apply(Cl, C -> yj^(q-1) * yl * product C));
  tst("all y_j^(q-1) x_C, |C|=c (l allowed)", ideal apply(subsets(drop(yv,{0,0}), c), C -> yj^(q-1) * product C));
  tst("all y_l^(q-1) x_C, |C|=c", ideal apply(subsets(drop(yv,{1,1}), c), C -> yl^(q-1) * product C));
  tst("all y_p^(q-1) x_C, p in P, |C|=c", ideal flatten apply(P, p -> apply(subsets(select(yv, v -> v != p), c), C -> p^(q-1) * product C)));
  tst("whole (q-1)-layer |A|=1", ideal flatten apply(yv, a -> apply(subsets(select(yv, v -> v != a), c), C -> a^(q-1) * product C)));
  if c + 2 <= n then tst("squarefree x_C, |C| >= c+2", ideal apply(subsets(yv, c+2), C -> product C));
  if odd n then tst("e_n(y)", ideal esym(yv, n));
  tst("(q-1)-layer + squarefree", ideal flatten apply(yv, a -> apply(subsets(select(yv, v -> v != a), c), C -> a^(q-1) * product C)) + (if c + 2 <= n then ideal apply(subsets(yv, c+2), C -> product C) else ideal(0_S)));
);
<< "FIN-OK" << endl;
