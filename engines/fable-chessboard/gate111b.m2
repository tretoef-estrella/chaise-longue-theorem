-- INFORME_9 STEP 4: K_(1,1,1)(7) alternatives, q = 9 (base = Q + box + N_0 in 7 vars; target 20370)
q = 9; nn = 7;
esym = (L,j) -> if j > #L or j < 0 then 0 else if j == 0 then 1 else sum apply(subsets(L,j), s -> product s);
psum = (L, e) -> sum apply(L, v -> v^e);
hsum = (L, e) -> sum apply(compositions(#L, e), c -> product apply(#L, i -> (L#i)^(c#i)));
layerN = (V, w) -> ( nv := #V; L := {};
  for a from 0 to nv do for b from max(1, a - w) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for B in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,B));
      L = append(L, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  if #L == 0 then ideal(0_(ring V#0)) else ideal L);
S = ZZ/3[x_1..x_7]; vs = gens S;
prs = select(flatten apply(vs, a -> apply(vs, b -> if a != b then {a,b} else null)), p -> p =!= null);
B = ideal apply(select(toList(1..nn), j -> odd j or j >= nn - 2), j -> esym(vs, j)) + ideal apply(vs, v -> v^q) + layerN(vs, 0);
t0 = currentTime(); << "base Q+box+N_0 : " << degree B << " in " << currentTime() - t0 << " s" << endl << flush;
cands = {
 {"y_j^(q-3) p_5(y-l)", ideal apply(prs, p -> (p#0)^(q-3) * psum(select(vs, v -> v != p#1), 5))},
 {"y_j^(q-3) e_5(y-l)", ideal apply(prs, p -> (p#0)^(q-3) * esym(select(vs, v -> v != p#1), 5))},
 {"y_j^(q-3) h_5(y-l)", ideal apply(prs, p -> (p#0)^(q-3) * hsum(select(vs, v -> v != p#1), 5))},
 {"y_j^(q-3) y_l^4 (exponent n-3)", ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^4)},
 {"y_j^(q-3) y_l^5 (again, control)", ideal apply(prs, p -> (p#0)^(q-3) * (p#1)^5)},
 {"y_j^(q-3) y_l^3 y_p^2 ...", ideal flatten apply(prs, p -> apply(select(vs, v -> v != p#0 and v != p#1), r -> (p#0)^(q-3) * (p#1)^3 * r^2))}};
for c in cands do ( t0 = currentTime(); << "  + " << c#0 << " : " << degree(B + c#1) << "  in " << currentTime() - t0 << " s" << endl << flush; );
<< "FIN-OK" << endl;
