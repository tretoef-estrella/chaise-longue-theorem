-- k=2 gate for the generic-row description: R_2 = L + (x_j^(q-2) e_2(V) : |V|=3, j in V)?  L = K'_2 + pz(M_2 : z^2). Cells (2,9), (2,27).
for q in {9, 27} do (
  S := ZZ/3[x_0..x_4]; X := gens S; e := j -> sum(subsets(X, j), s -> product s);
  I5 := ideal(e 1, e 3, e 5) + ideal apply(X, u -> u^q);
  Mgen := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
  M2 := ideal(Mgen(toList(0..4), 1) | Mgen(toList(0..4), 2)); K2 := I5 + M2; z := x_4;
  S4 := ZZ/3[y_0..y_3]; pz := map(S4, S, {y_0,y_1,y_2,y_3,0}); Y := gens S4; e4 := j -> sum(subsets(Y, j), s -> product s);
  R2 := pz((K2 + ideal(z^3)) : z^2);
  Mgen4 := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> Y#i) * product(A, i -> (Y#i)^(q-1)))); L);
  Kp2 := ideal(e4 1, e4 3) + ideal apply(Y, u -> u^q) + ideal(e4 4) + ideal Mgen4(toList(0..3), 1);
  L := Kp2 + pz(M2 : z^2);
  guess := ideal flatten for V in subsets(toList(0..3), 3) list for j in V list ( (Y#j)^(q-2) * sum(subsets(V, 2), s -> product(s, i -> Y#i)) );
  << "q=" << q << ": colength R2 = " << degree R2 << " (12(q-2) = " << 12*(q-2) << "), colength L = " << degree L << ", colength L + guess = " << degree(L + guess) << ", L + guess == R2? " << toString((L + guess) == R2) << endl << flush;
  Ga := ideal flatten for i from 0 to 3 list for j from 0 to 3 list if i == j then continue else (Y#i)^2*(Y#j)^(q-2);
  << "   L + G-a elements == R2? " << toString((L + Ga) == R2) << endl << flush;);
<< "FIN-OK" << endl; exit 0
