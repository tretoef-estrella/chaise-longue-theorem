-- generadores minimos de R_{q-1} (par) y R'_{q-1} (impar), expresados en las 2k (resp. 2k-1) variables
rowP = (k,q) -> (
  n := 2*k+2; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  Ra := f2(J1 : (x_(n-2))^(q-1));
  G := flatten entries mingens Ra;
  << "PAR (k,q)=(" << k << "," << q << ") r_{q-1}=" << numColumns basis(S2/Ra) << "  #mingens=" << #G << " degs=" << toString apply(G, g -> first degree g) << endl;
  scan(G, g -> if first degree g < q then << "   " << toString g << endl else << "   [deg " << first degree g << "] lead " << toString leadTerm g << "  #terms " << #terms g << endl);
  << flush;
);
rowI = (k,q) -> (
  n := 2*k+1; S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  Ra := f2(J1 : (x_(n-2))^(q-1));
  G := flatten entries mingens Ra;
  << "IMPAR (k,q)=(" << k << "," << q << ") r'_{q-1}=" << numColumns basis(S2/Ra) << "  #mingens=" << #G << " degs=" << toString apply(G, g -> first degree g) << endl;
  scan(G, g -> if first degree g < q then << "   " << toString g << endl else << "   [deg " << first degree g << "] lead " << toString leadTerm g << "  #terms " << #terms g << endl);
  << flush;
);
rowP(1,9); rowP(2,9); rowP(2,27); rowP(3,3);
rowI(1,9); rowI(2,9); rowI(2,27); rowI(3,3);
<< "FIN-OK" << endl; exit 0
