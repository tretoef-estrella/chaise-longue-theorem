-- Cell (3,9): are the "G-a times a variable" elements in the generic row of K_3?  z = x_6.
-- Test: z^2 * x_c * x_i^2 * x_j^(q-2) in K_3 + (z^3) for {c,i,j} distinct in 0..5, and also the pure G-a shape z^2*x_i^2*x_j^(q-2) (should fail if the row is exact).
q = 9; S = ZZ/3[x_0..x_6]; X = gens S; e = j -> sum(subsets(X, j), s -> product s);
I7 = ideal(e 1, e 3, e 5, e 7) + ideal apply(X, u -> u^q);
Mgen = (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
M3 = ideal(Mgen(toList(0..6), 1) | Mgen(toList(0..6), 2) | Mgen(toList(0..6), 3));
K3 = I7 + M3; z = x_6;
KK = K3 + ideal(z^3);
<< "gb of K3+(z^3) ..." << endl << flush;
G = gb KK;
<< "done gb" << endl << flush;
tst = (f, lab) -> << lab << " in K3+(z^3)? " << toString(f % G == 0) << endl << flush;
tst(z^2*x_0*x_1^2*x_2^(q-2), "z^2 x0 x1^2 x2^(q-2)");
tst(z^2*x_1^2*x_2^(q-2), "z^2 x1^2 x2^(q-2)  (pure G-a shape)");
tst(z^2*x_0*x_3*x_1^2*x_2^(q-2), "z^2 x0 x3 x1^2 x2^(q-2)");
tst(z^2*x_0*x_1^3*x_2^(q-3), "z^2 x0 x1^3 x2^(q-3)");
tst(z^2*x_0*x_1^2*x_2^(q-2)*x_3^(q-1), "z^2 x0 x1^2 x2^(q-2) x3^(q-1)");
tst(z^2*x_0*x_1*x_2^(q-1), "z^2 x0 x1 x2^(q-1)  (M'-type, should be in)");
-- row-1 check: z * x0x1x2x3x4x5 in K3 ? (e_7 => yes)
tst(z*x_0*x_1*x_2*x_3*x_4*x_5, "z*e6 (should be in)");
<< "FIN-OK" << endl; exit 0
