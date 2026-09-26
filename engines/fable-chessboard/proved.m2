-- PROVED element of the generic row for all k: x_j^(q-2) * e_{2k-2}(x_0..x_{2k-1}) in R_2 = pz(K_k : z^2). Is it outside L = K'_k + pz(M_k : z^2), and how much does it cut? Cells (2,9), (2,27), (3,9).
runcell = (k, q) -> (
  n := 2*k+1; S := ZZ/3[x_0..x_(n-1)]; X := gens S; e := j -> sum(subsets(X, j), s -> product s);
  I := ideal apply(select(toList(1..n), j -> j % 2 == 1), j -> e j) + ideal apply(X, u -> u^q);
  Mgen := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
  M := ideal flatten apply(toList(1..k), j -> Mgen(toList(0..n-1), j)); K := I + M; z := X#(n-1);
  KK := K + ideal(z^3); G := gb KK;
  xp := drop(X, -1); ee := j -> sum(subsets(xp, j), s -> product s);
  pv := apply(2*k, j -> z^2 * (X#j)^(q-2) * ee(2*k-2));
  << "(" << k << "," << q << "): all proved elements z^2 x_j^(q-2) e_{2k-2}(x') in K_k+(z^3)? " << toString all(pv, f -> f % G == 0) << endl << flush;
  S2 := ZZ/3[y_0..y_(2*k-1)]; pz := map(S2, S, (gens S2) | {0_S2}); Y := gens S2; e2 := j -> sum(subsets(Y, j), s -> product s);
  Mgen2 := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> Y#i) * product(A, i -> (Y#i)^(q-1)))); L);
  Kp := ideal apply(select(toList(1..2*k), j -> j % 2 == 1), j -> e2 j) + ideal apply(Y, u -> u^q) + ideal(e2(2*k)) + ideal flatten apply(toList(1..min(2,k-1)), j -> Mgen2(toList(0..2*k-1), j));
  L := Kp + pz(M : z^2);
  pe := ideal apply(2*k, j -> (Y#j)^(q-2) * e2(2*k-2));
  << "   proved elements in L? " << toString isSubset(pe, L) << "; colength L = " << degree L << ", colength L + proved = " << degree(L + pe) << endl << flush;);
runcell(2, 9); runcell(2, 27); runcell(3, 9);
<< "FIN-OK" << endl; exit 0
