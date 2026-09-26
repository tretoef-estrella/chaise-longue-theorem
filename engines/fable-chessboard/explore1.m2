ex = (k,q) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1), MonomialOrder=>GRevLex];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, v -> v^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  << "== (k,q)=(" << k << "," << q << ")" << endl;
  << "in(I) gens: " << toString flatten entries gens gb I << endl;
  << "in(I) leading: " << toString flatten entries leadTerm gens gb I << endl;
  G := flatten entries gens gb J1;
  << "J1 GB (" << #G << " elems): " << toString G << endl;
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  scan({0,1,2,q-2,q-1}, a -> (
     Ra := f2(J1 : (x_(n-2))^a);
     << "a=" << a << " R_a GB: " << toString flatten entries gens gb Ra << "  std: " << toString flatten entries basis(S2/Ra) << endl;));
);
ex(1,9); ex(1,27);
<< "FIN-OK" << endl; exit 0
