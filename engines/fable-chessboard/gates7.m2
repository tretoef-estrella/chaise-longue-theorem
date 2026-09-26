-- INFORME_9 STEP 4 (PART C): gates in 7 variables, q = 9: K_(2,1)(7) -> 12390 ; K_(1,1,1)(7) -> 20370
q = 9;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
famA = (V, d) -> ( nv := #V; L := {}; for j from 0 to nv-1 do for l from 0 to nv-1 do if j != l then L = append(L, (V#j)^(q-2) * esym(select(V, v -> v != V#l), d)); if #L == 0 then ideal(0_(ring V#0)) else ideal L);
S = ZZ/3[x_1..x_7]; vs = gens S; nn = 7;
t0 = currentTime();
K21 = ideal apply(select(toList(1..nn), j -> odd j or j >= nn - 2), j -> esym(vs, j)) + ideal apply(vs, v -> v^q) + layerN(vs, 1) + famA(vs, nn - 3);
<< "K_(2,1)(7): colength " << degree K21 << "  (target 12390)  in " << currentTime() - t0 << " s" << endl << flush;
t0 = currentTime();
K111 = ideal apply(select(toList(1..nn), j -> odd j or j >= nn - 2), j -> esym(vs, j)) + ideal apply(vs, v -> v^q) + layerN(vs, 0) + ideal flatten apply(vs, a -> apply(vs, b -> if a != b then a^(q-3) * b^(nn-2) else 0_S));
<< "K_(1,1,1)(7): colength " << degree K111 << "  (target 20370)  in " << currentTime() - t0 << " s" << endl << flush;
<< "FIN-OK" << endl;
