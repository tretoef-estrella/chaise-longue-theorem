-- (G-a_3) direct check at (3,9): z^2 x_0^2 x_1^(q-2) e_2(x_1..x_5) in K_3 + (z^3)? (implied by int39d through the reduction lemma; this validates the algebra)
q = 9; S = ZZ/3[x_0..x_6]; X = gens S; e = j -> sum(subsets(X, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
K3 = I7 + ideal(Mgen(toList(0..6), 1) | Mgen(toList(0..6), 2) | Mgen(toList(0..6), 3)); z = x_6;
G = gb(K3 + ideal(z^3));
V = {x_1,x_2,x_3,x_4,x_5}; e2V = sum(subsets(V, 2), s -> product s);
<< "(G-a_3) z^2 x0^2 x1^(q-2) e_2(x1..x5) in K3+(z^3)? " << toString((z^2*x_0^2*x_1^(q-2)*e2V) % G == 0) << endl;
<< "control: z^2 x0^2 x1^(q-2) x2 x3 in K3+(z^3)? " << toString((z^2*x_0^2*x_1^(q-2)*x_2*x_3) % G == 0) << endl;
<< "control: z^2 x0^2 x1^(q-2) e_2(x2..x5) (j outside e_2) in K3+(z^3)? " << toString((z^2*x_0^2*x_1^(q-2)*sum(subsets({x_2,x_3,x_4,x_5}, 2), s -> product s)) % G == 0) << endl;
<< "FIN-OK" << endl; exit 0
