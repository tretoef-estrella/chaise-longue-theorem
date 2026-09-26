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
cells = value get "eng7.cells";
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
);
<< "FIN-OK" << endl;
