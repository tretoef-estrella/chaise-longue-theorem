-- Cell (3,9): dim S_7/K_3 vs N_3 = 37947 (= 7761 + 4266 + 6*3930 + 2340, fibre counts) and dim S_6/K'_3 vs N'_3 = 4266.
q = 9;
S6 = ZZ/3[y_0..y_5]; Y = gens S6; e6 = j -> sum(subsets(Y, j), s -> product s);
Mgen6 = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> Y#i) * product(A, i -> (Y#i)^(q-1)))); L);
Kp3 = ideal(e6 1, e6 3, e6 5) + ideal apply(Y, u -> u^q) + ideal(e6 6) + ideal(Mgen6(toList(0..5),1) | Mgen6(toList(0..5),2));
<< "dim S6/K'_3 = " << degree Kp3 << "   (N'_3 = 4266)" << endl << flush;
S = ZZ/3[x_0..x_6]; X = gens S; e = j -> sum(subsets(X, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
K3 = I7 + ideal(Mgen(toList(0..6), 1) | Mgen(toList(0..6), 2) | Mgen(toList(0..6), 3));
<< "dim S7/K_3 = " << degree K3 << "   (N_3 = 37947)" << endl << flush;
<< "FIN-OK" << endl; exit 0
