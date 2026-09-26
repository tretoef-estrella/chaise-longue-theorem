-- MISSION 10: (G1) for m>=2 as a FIRST-ORDER algebraic statement (no W, no z):
-- find A_r (deg d-2r-1) with  sum A_r e_{2r+1} in J := Ntilde_{m-1}(n) + box + (e_n)   and   s == sum A_r e_{2r} mod B,
-- B := (e_k : k odd or k >= n-m) + box + N_{m-1}(n).
esym = (L,j) -> if j > #L or j < 0 then 0_(ring L#0) else if j == 0 then 1_(ring L#0) else sum apply(subsets(L,j), s -> product s);
layerIdeal = (V, w, q) -> ( nv := #V; out := {};
  for a from 0 to nv do for b from 1 to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w then
    for A in subsets(nv, a) do for Bs in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,Bs));
      out = append(out, (product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))))));
  ideal mingens ideal out);
expsOf = (n, dd, q) -> if n == 0 then (if dd == 0 then {{}} else {}) else flatten apply(toList(0..min(dd,q-1)), a -> apply(expsOf(n-1, dd-a, q), e -> prepend(a, e)));
setupAlg = (q, n, m) -> (
  c := n - m - 1; d := q + c - 1;
  S := ZZ/3[y_1..y_n, MonomialOrder => GRevLex]; ys := gens S;
  Nl := layerIdeal(ys, m-1, q);
  box := ideal apply(ys, v -> v^q);
  J := Nl + box + ideal(esym(ys, n));
  B := ideal(apply(select(toList(1..n), k -> odd k or k >= n-m), k -> esym(ys,k))) + box + Nl;
  GJ := gb J; GB := gb B;
  s := (ys#0)^(q-2) * esym(drop(ys, {1,1}), c);
  (S, ys, c, d, J, B, GJ, GB, s));
-- solve with a given list of unknown pairs (A-vector as list of polys indexed by r)
solveAlg = (S, ys, d, GJ, GB, s, cands) -> (
  n := #ys;
  tops := apply(cands, A -> (sum apply(#A, r -> A#r * esym(ys, 2*r+1))) % GJ);
  shs := apply(cands, A -> (sum apply(#A, r -> A#r * esym(ys, 2*r))) % GB);
  ns := s % GB;
  -- stack: top part must vanish, shadow part must equal ns; use a tag variable-free trick: two coefficient blocks
  (mt, Ct) := coefficients matrix{tops | {0_S}};
  (ms, Cs) := coefficients matrix{shs | {ns}};
  Mfull := Ct || Cs;
  Mfull = sub(Mfull, ZZ/3);
  k := numcols Mfull;
  M := submatrix(Mfull, toList(0..k-2)); v := submatrix(Mfull, {k-1});
  sol := v // M;
  (M * sol == v, M, sol));
