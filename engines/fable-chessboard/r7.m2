load "m11lib.m2";
-- R7: the layer N_1(n) of (2,1^(L-2)) children.  (a) redundant in the child itself?  (b) small ansatz: m = a^(q-1) x_C (B = {b1,b2}) as
--   sum of [monomial in (a,b1,b2)] * X'_{pp'} (families of (1^L), all pairs) + e_k(y)*anything + sqfree*anything + box
runF = (q, n, L) -> (
  S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S;
  nu := {2} | toList((L-2):1);
  Kc := clK(ys, q, nu);  noLay := clQ(ys, nu) | apply(ys, v -> v^q) | clFam(ys, q, nu);
  G0 := gb ideal noLay; lay := clLayer(ys, 1, q);
  << "q=" << q << " n=" << n << " child " << toString nu << " : layer N_1 redundant in Q+box+F? " << all(lay, g -> g % G0 == 0);
  G1 := gb ideal(noLay | clLayer(ys, 0, q));
  << " ; redundant in Q+box+F+N_0? " << all(lay, g -> g % G1 == 0) << endl;
  -- (b) ansatz
  a := ys#0; b1 := ys#1; b2 := ys#2; m := a^(q-1) * product drop(ys, 3);
  base := apply(select(toList(1..n), k -> odd k or k >= n-L+1), k -> clE(ys,k)) | apply(ys, v -> v^q) | apply(ys, b -> product delete(b, ys));
  Gb := gb ideal base;
  fams := flatten apply(toList(0..n-1), j -> apply(select(toList(0..n-1), l -> l != j), l -> (j,l)));
  dX := q + n - L - 2; dm := q - 1 + n - 3;
  mons := flatten entries basis(dm - dX, ZZ/3[w_1..w_3]);
  cands := {}; labs := {};
  for pr in fams do for mo in mons do ( ex := first exponents mo; cands = append(cands, a^(ex#0) * b1^(ex#1) * b2^(ex#2) * clPhi(ys, q, L, n-2, pr#0, pr#1)); labs = append(labs, (pr, ex)));
  red := apply(cands, c -> c % Gb);
  (mm, C) := coefficients matrix{red | {m % Gb}};
  C = sub(C, ZZ/3); k := numcols C; M := submatrix(C, toList(0..k-2)); v := submatrix(C, {k-1});
  sol := v // M; ok := (M*sol == v);
  << "   ansatz (multipliers in a,b1,b2 only) solvable? " << ok << " (" << #cands << " unknowns)" << endl;
  if ok then (
    cur := select(toList(0..#cands-1), i -> sol_(i,0) != 0);
    for i in reverse cur do ( tr := delete(i, cur); M2 := submatrix(M, tr); s2 := v // M2; if M2*s2 == v then cur = tr );
    M3 := submatrix(M, cur); s3 := v // M3;
    for ii from 0 to #cur-1 do << "      " << s3_(ii,0) << " * " << toString (labs#(cur#ii)) << endl;
  );
  << flush;
);
runF(9,4,2); runF(9,5,2); runF(9,5,3); runF(9,6,3); runF(9,6,4); runF(27,5,3);
<< "FIN-OK" << endl;
