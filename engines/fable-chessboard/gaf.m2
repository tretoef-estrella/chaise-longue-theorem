-- Geometric side of G-a at k=2: is y0^2*y1^(q-2) a function of degree <= q-1 on W_v = perm(-v,-1,c,-c) subset F_q^4 (v generic)?
-- Linear algebra on the evaluation matrix (no enumeration of F_q^4: points built from the multiset). q = 9, 27.
for q in {9, 27} do (
  F := GF(q, Variable=>w); v := w; els := toList apply(q, i -> if i == 0 then 0_F else w^i);
  pts := unique flatten for c in els list flatten for p in permutations {-v, -1_F, c, -c} list {p};
  R := F[y_0..y_3];
  mons := flatten entries basis(0, q-1, R);   -- all monomials of degree <= q-1
  E := matrix apply(pts, p -> apply(mons, m -> sub(m, matrix{p})));   -- |pts| x #mons
  target := matrix apply(pts, p -> {sub(y_0^2*y_1^(q-2), matrix{p})});
  sol := target // E; ok := (E*sol == target);
  << "q=" << q << " |W_v|=" << #pts << " monomials<=q-1: " << #mons << " rank E = " << rank E << "  y0^2 y1^(q-2) of degree <= q-1 on W_v? " << toString ok << endl << flush;
  -- also the Hilbert function of W_v in degree q-1 vs q: does degree q-1 already exhaust Fun(W_v)?
  << "   functions of degree <= q-1 span dim " << rank E << " of |W_v| = " << #pts << endl << flush;);
<< "FIN-OK" << endl; exit 0
