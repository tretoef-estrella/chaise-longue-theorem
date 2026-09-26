ex = (k,q,lista) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, v -> v^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  << "== (k,q)=(" << k << "," << q << ")" << endl;
  G := flatten entries gens gb J1;
  << "J1 GB (" << #G << " elems), leading terms: " << toString flatten entries leadTerm gens gb J1 << endl;
  << "J1 GB degrees: " << toString apply(G, g -> first degree g) << endl;
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  scan(lista, a -> (
     Ra := f2(J1 : (x_(n-2))^a);
     Gr := flatten entries gens gb Ra;
     << "a=" << a << " r_a=" << numColumns basis(S2/Ra) << " R_a GB (" << #Gr << "): " << toString Gr << endl;
     << "   leading: " << toString flatten entries leadTerm gens gb Ra << endl;
     << "   hilbert: " << toString apply(toList(0..2*q), d -> hilbertFunction(d, S2/Ra)) << endl;));
);
ex(2,9,{0,1,2,7,8});
<< "FIN-OK" << endl; exit 0
