-- INFORME_9 STEP 1: engine test for (G1). Cell (nn, m): n = nn-1 variables y, z = x_nn.
-- (a) raw: z^2 * s in E := I^{(nn)} + z*Ntilde_{m-1}(n) + (z^3) ?   (b) structured: shadows of u = y_i syzygies.
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
cells = value get "eng1.cells";
for cell in cells do (
  nn = cell#0; m = cell#1; n = nn - 1; c = n - m - 1; d = q + n - m - 2;
  << "=== cell (" << nn << "," << m << ") q=" << q << "  n=" << n << " c=" << c << " d=" << d << endl << flush;
  S = ZZ/3[x_1..x_nn]; vs = gens S; z = x_nn; yv = take(vs, n);
  Iodd = ideal apply(select(toList(1..nn), j -> odd j), j -> esym(vs, j)) + ideal apply(vs, v -> v^q);
  Nt = layerN(yv, m-1); if (odd n and m >= 1) then Nt = Nt + ideal esym(yv, n);
  E = Iodd + z*Nt + ideal(z^3);
  t0 = currentTime(); Eg = gb E; << "gb E: " << currentTime() - t0 << " s" << endl << flush;
  s = (yv#0)^(q-2) * esym(drop(yv, {1,1}), c);
  raw = ((z^2 * s) % Eg) == 0;
  << "RAW ENGINE: z^2*s in I+z*Ntilde+(z^3)? " << raw << endl << flush;
  -- control: with N_{m-2}(n) added (full row formula)
  if m >= 2 then ( E2 = E + layerN(yv, m-2); << "  with N_{m-2}: " << (((z^2 * s) % E2) == 0) << endl << flush; );
  -- (b) structured ansatz in n variables
  T = ZZ/3[x_1..x_n]; yy = gens T; inc = map(S, T, yv);
  J = layerN(yy, m-1) + ideal apply(yy, v -> v^q); if (odd n and m >= 1) then J = J + ideal esym(yy, n);
  Jg = gb J;
  known = ideal apply(select(toList(1..n), j -> odd j or j >= n - m), j -> esym(yy, j)) + J;
  Qf = i -> product apply(select(yy, v -> v != yy#i), v -> yy#i + v);
  gmons = flatten entries basis(q - m - 2, T);
  L = flatten apply(toList(0..n-1), i -> apply(gmons, g -> {i, g}));
  nfs = apply(L, p -> (p#1 * yy#(p#0) * Qf(p#0)) % Jg);
  (mons, cf) = coefficients(matrix{nfs}); cf = lift(cf, ZZ/3);
  kk = gens ker cf;
  << "structured: " << #L << " candidates (u=y_i, g monomial deg " << q-m-2 << "); kernel dim " << numcols kk << endl << flush;
  shadows = apply(numcols kk, j -> sum apply(#L, i -> (lift(kk_(i,j), ZZ) % 3) * (L#i#1) * Qf(L#i#0)));
  shadows = select(shadows, f -> f != 0);
  ss = (yy#0)^(q-2) * esym(drop(yy, {1,1}), c);
  Rk = known + (if #shadows == 0 then ideal(0_T) else ideal shadows);
  << "STRUCTURED (u=y_i): s in known + shadows? " << ((ss % Rk) == 0) << "  ; s in known alone? " << ((ss % known) == 0) << endl << flush;
  -- which u's are needed: only u in {y_j, y_l}?
  Ljl = select(toList(0..#L-1), i -> member(L#i#0, {0,1}));
  cf2 = cf_Ljl; kk2 = gens ker cf2;
  sh2 = select(apply(numcols kk2, j -> sum apply(#Ljl, i -> (lift(kk2_(i,j), ZZ) % 3) * (L#(Ljl#i)#1) * Qf(L#(Ljl#i)#0))), f -> f != 0);
  Rk2 = known + (if #sh2 == 0 then ideal(0_T) else ideal sh2);
  << "STRUCTURED (u in {y_j,y_l} only): kernel dim " << numcols kk2 << " ; s in known + shadows? " << ((ss % Rk2) == 0) << endl << flush;
  Lj = select(toList(0..#L-1), i -> L#i#0 == 0);
  cf3 = cf_Lj; kk3 = gens ker cf3;
  sh3 = select(apply(numcols kk3, j -> sum apply(#Lj, i -> (lift(kk3_(i,j), ZZ) % 3) * (L#(Lj#i)#1) * Qf(0))), f -> f != 0);
  Rk3 = known + (if #sh3 == 0 then ideal(0_T) else ideal sh3);
  << "STRUCTURED (u = y_j only): kernel dim " << numcols kk3 << " ; s in known + shadows? " << ((ss % Rk3) == 0) << endl << flush;
);
<< "FIN-OK" << endl;
