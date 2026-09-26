load "m11lib.m2";
-- R3c: the (T) half for (1^ell): T := sum_r A_r e_{2r+1}(y), A_r = (-1)^c H_{D_r}(-a,b).  Is T == sum alpha_{pp'} X_{pp'} (scalars) mod box + (e_k(y): k >= c+2)?
Hh = (D, u, b, q) -> sum apply(toList(1..D-1), i -> if i <= q-1 and D-i <= q-1 then u^i * b^(D-i) else 0);
runC = (q, np1, ell) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S; a := ys#0; b := ys#1; u := -a;
  c := n - ell - 1; N := q + c - 2; R := c // 2;
  T := sum apply(toList(0..R), r -> (-1)^c * Hh(N - 2*r, u, b, q) * clE(ys, 2*r+1));
  Sh := sum apply(toList(0..R), r -> (-1)^c * Hh(N - 2*r, u, b, q) * clE(ys, 2*r));
  Gb0 := gb ideal(apply(ys, v -> v^q) | apply(select(toList(1..n), k -> k >= c+2), k -> clE(ys,k)));
  pairs := flatten apply(toList(0..n-1), j -> apply(select(toList(0..n-1), l -> l != j), l -> (j,l)));
  Xs := apply(pairs, pr -> clPhi(ys, q, ell, n-2, pr#0, pr#1) % Gb0);
  (mm, C) := coefficients matrix{Xs | {T % Gb0}};
  C = sub(C, ZZ/3); k := numcols C;
  M := submatrix(C, toList(0..k-2)); v := submatrix(C, {k-1});
  sol := v // M;
  ok := (M*sol == v);
  << "q=" << q << " (1^" << ell << ") n+1=" << np1 << " c=" << c << " : T == scalar comb of X_pp' mod box+e_{>=c+2}? " << ok << endl;
  if ok then for i from 0 to #pairs-1 do if sol_(i,0) != 0 then << "    " << sol_(i,0) << " * X_" << toString pairs#i << endl;
  -- also check (Sh) directly: Sh == X' mod B
  GB := gb ideal(apply(ys, v -> v^q) | apply(select(toList(1..n), k -> odd k or k >= n-ell), k -> clE(ys,k)));
  << "   (Sh) Sh - X'_{12} in B: " << ((Sh - clPhi(ys, q, ell+1, n-2, 0, 1)) % GB == 0) << endl << flush;
);
runC(9,5,2); runC(9,6,2); runC(9,7,2); runC(9,6,3); runC(9,7,3); runC(9,7,4); runC(27,5,2); runC(27,6,2); runC(27,6,3);
<< "FIN-OK" << endl;
