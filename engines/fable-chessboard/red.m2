-- Reduction test: x_i^2 x_j^(q-1) e_{2k-3}(x' minus {i,j}) in K'_k ?  (then x_i x_j^(q-2) e_{2k-2}(x') is in the even generic row). Cells (2,9), (2,27), (3,9).
runcell = (k, q) -> (
  n := 2*k; S := ZZ/3[y_0..y_(n-1)]; Y := gens S; e := j -> sum(subsets(Y, j), s -> product s);
  Mgen := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> Y#i) * product(A, i -> (Y#i)^(q-1)))); L);
  Kp := ideal apply(select(toList(1..n), j -> j % 2 == 1), j -> e j) + ideal apply(Y, u -> u^q) + ideal(e n) + ideal flatten apply(toList(1..min(2,k-1)), j -> Mgen(toList(0..n-1), j));
  G := gb Kp;
  rest := toList(set Y - set {Y#0, Y#1}); er := sum(subsets(rest, 2*k-3), s -> product s);
  f := (Y#0)^2 * (Y#1)^(q-1) * er;
  << "(" << k << "," << q << "): y_0^2 y_1^(q-1) e_{2k-3}(others) in K'_k? " << toString(f % G == 0) << endl << flush;
  g := (Y#0)^2 * (Y#1)^(q-1) * (Y#2)^(2*k-3);
  << "   (control) y_0^2 y_1^(q-1) y_2^(2k-3) in K'_k? " << toString(g % G == 0) << endl << flush;);
runcell(2, 9); runcell(2, 27); runcell(3, 9);
<< "FIN-OK" << endl; exit 0
