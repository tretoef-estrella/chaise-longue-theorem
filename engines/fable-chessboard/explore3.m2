ex = (k,q,full) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, v -> v^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  << "== (k,q)=(" << k << "," << q << ")" << endl;
  G := flatten entries gens gb J1;
  << "J1 GB leading terms: " << toString flatten entries leadTerm gens gb J1 << endl;
  if full then scan(G, g -> (
     if first degree g >= 4 and first degree g < 2*q then (
        << "--- deg " << first degree g << " lead " << toString leadTerm g << endl;
        -- print g arranged by powers of x_4
        d := first degree g;
        scan(reverse toList(0..d), e -> (
           c := 0;
           ));
        << toString g << endl;)));
);
ex(2,9,true); ex(2,27,false);
<< "FIN-OK" << endl; exit 0
