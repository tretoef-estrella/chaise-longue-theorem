chk = (q) -> (
  S := ZZ/3[x_0..x_3]; x := gens S;
  el := j -> sum(subsets(x, j), product);
  I4 := ideal(el 1, el 3) + ideal apply(x, v -> v^q);
  M := ideal flatten apply(4, a -> apply(subsets(select(toList(0..3), i -> i != a), 2), C -> product(C, i -> x#i) * x#a^(q-1)));
  K := I4 + ideal(el 4) + M;
  Y := ZZ/3[y_0,y_1,y_2]; psi := map(Y, S, {y_0,y_1,y_2, -(y_0+y_1+y_2)});
  Kb := psi K; e1 := y_0+y_1+y_2;
  rows := apply(toList(0..q-1), a -> numColumns basis(Y/((Kb : e1^a) + ideal e1)));
  << "q=" << q << ": rows of K'_2 via psi: " << toString rows << "  sum=" << sum rows << "  N'_2=" << (if q==9 then 88 else 304) << endl;
  Rq := (Kb : e1^(q-1)) + ideal e1;
  << "   m^2 in R'^K_{q-1}? " << toString(all({y_0*y_1, y_0*y_2, y_1*y_2, y_0^2, y_1^2, y_2^2}, f -> f % Rq == 0)) << "   dim=" << numColumns basis(Y/Rq) << endl;
  -- direct check without psi: rows as pi'(K : x_3^a)
  S3 := ZZ/3[x_0,x_1,x_2]; f3 := map(S3, S, gens S3 | {0_S3});
  rows2 := apply(toList(0..q-1), a -> numColumns basis(S3/f3(K : x_3^a)));
  << "   direct rows pi'(K':x_3^a): " << toString rows2 << endl << flush;
);
chk(9); chk(27);
<< "FIN-OK" << endl; exit 0
