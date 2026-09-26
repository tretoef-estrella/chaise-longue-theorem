-- Odd side at (3,9): generic row R'_2 = pz((K'_3 + (z^3)) : z^2) of K'_3 along z = x_5, colength vs |W'_gen|, and generators beyond the sum of colons L' = pz(I6 : z) + pz(M'_3 : z^2) + (e_5(x'')) [INFORME_3 3.2].
q = 9; S = ZZ/3[x_0..x_5]; X = gens S; e = j -> sum(subsets(X, j), s -> product s);
I6 = ideal(e 1, e 3, e 5) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
Mp3 = ideal(Mgen(toList(0..5), 1) | Mgen(toList(0..5), 2));
Kp3 = I6 + ideal(e 6) + Mp3; z = x_5;
S5 = ZZ/3[y_0..y_4]; pz = map(S5, S, {y_0,y_1,y_2,y_3,y_4,0}); Y = gens S5; e5 = j -> sum(subsets(Y, j), s -> product s);
Rp2 = pz((Kp3 + ideal(z^3)) : z^2); << "odd generic row colength = " << degree Rp2 << endl << flush;
Rp1 = pz((Kp3 + ideal(z^2)) : z); << "odd row 1 colength = " << degree Rp1 << "  (should be N_2(9) = 855)" << endl << flush;
Lp = pz((I6 + ideal(z^2)) : z) + pz(Mp3 : z^2) + ideal(e5 5);
<< "L' subset R'_2? " << toString isSubset(Lp, Rp2) << ", colength L' = " << degree Lp << endl << flush;
G = flatten entries mingens Rp2; extra = select(G, g -> g % Lp != 0);
<< "minimal generators of R'_2: " << #G << "; not in L': " << #extra << "; degrees: " << toString sort apply(extra, degree) << endl << flush;
for g in take(extra, 8) do << "   " << toString g << endl;
<< "FIN-OK" << endl; exit 0
