-- k=2 gate for the k-general guess: z^2 * y_j^(q-2) * e_{2k-2}(2k-1 of the 2k variables, j among them) in K_k + (z^3)?
-- k=2: z = x_4, 2k variables x_0..x_3, e_2 of three of them. Also test the pieces separately. q = 9, 27.
for q in {9, 27} do (
  S := ZZ/3[x_0..x_4]; X := gens S; e := j -> sum(subsets(X, j), s -> product s);
  I5 := ideal(e 1, e 3, e 5) + ideal apply(X, u -> u^q);
  Mgen := (V, j) -> ( L := {}; for A in subsets(V, j) do for B in subsets(toList(set V - set A), j) do ( C := toList(set V - set A - set B); L = append(L, product(C, i -> X#i) * product(A, i -> (X#i)^(q-1)))); L);
  K2 := I5 + ideal(Mgen(toList(0..4), 1) | Mgen(toList(0..4), 2)); z := x_4;
  KK := K2 + ideal(z^3); G := gb KK;
  tst := (f, lab) -> << "q=" << q << ": " << lab << " in K2+(z^3)? " << toString(f % G == 0) << endl << flush;
  e2 := (a,b,c) -> a*b + a*c + b*c;
  tst(z^2 * x_1^(q-2) * e2(x_0, x_1, x_2), "z^2 x1^(q-2) e_2(x0,x1,x2)   [guess, k=2]");
  tst(z^2 * x_1^(q-2) * x_0 * x_2, "z^2 x0 x2 x1^(q-2)");
  tst(z^2 * x_1^(q-1) * (x_0 + x_2), "z^2 (x0+x2) x1^(q-1)");
  tst(z^2 * x_0^2 * x_1^(q-2), "z^2 x0^2 x1^(q-2)   [G-a]");
  tst(z^2 * x_1^(q-2) * e2(x_0, x_2, x_3), "z^2 x1^(q-2) e_2(x0,x2,x3)  [j outside]");
  tst(z^2 * x_1^(q-2) * (x_0^2 + x_0*x_2 + x_2^2), "z^2 x1^(q-2) h_2(x0,x2)");
  );
<< "FIN-OK" << endl; exit 0
