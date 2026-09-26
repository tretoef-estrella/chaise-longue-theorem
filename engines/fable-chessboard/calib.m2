fil = (k,q) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, v -> v^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J0 := f1(I); J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  r := apply(toList(0..q-1), a -> numColumns basis(S2/f2(J1 : (x_(n-2))^a)));
  << "(k,q)=(" << k << "," << q << ") r=" << r << " suma=" << sum r << endl << flush;
);
fil(1,9); fil(2,3);
<< "FIN-OK" << endl; exit 0
