rowIdeal = (n,q) -> (
  S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  (S2, f2(J1 : (x_(n-2))^(q-1)))
);
interQ = (S2,q) -> ( m := numgens S2; y := gens S2;
  oddj := select(toList(1..m-2), j -> odd j);
  intersect apply(subsets(m,2), ij -> ( rest := select(y, u -> not member(u, {y#(ij#0), y#(ij#1)}));
      ideal(y#(ij#0), y#(ij#1)) + ideal(apply(oddj, j -> sum(subsets(rest, j), s -> product s))) + ideal(apply(y, u -> u^q)))));
candQ = (S2,q) -> ( m := numgens S2; y := gens S2;
  oddj := select(toList(1..m), j -> odd j);
  ideal(apply(oddj, j -> sum(subsets(y, j), s -> product s))) + ideal(apply(subsets(y, m-1), s -> product s)) + ideal(apply(y, u -> u^q)));
-- (2,27) par
(S2,R) = rowIdeal(6,27); Q = interQ(S2,27); C = candQ(S2,27);
<< "(2,27) par: r=" << numColumns basis(S2/R) << " dim S/Q=" << numColumns basis(S2/Q) << " Q==R? " << toString(Q==R) << " | cand (e_odd, sqfree 2k-1, caja): dim=" << numColumns basis(S2/C) << " C==R? " << toString(C==R) << endl << flush;
(S2,R) = rowIdeal(6,9); C = candQ(S2,9);
<< "(2,9) par: cand dim=" << numColumns basis(S2/C) << " C==R? " << toString(C==R) << endl << flush;
(S2,R) = rowIdeal(8,3); C = candQ(S2,3);
<< "(3,3) par: r=" << numColumns basis(S2/R) << " cand dim=" << numColumns basis(S2/C) << " C==R? " << toString(C==R) << " C⊆R? " << toString(isSubset(C,R)) << endl << flush;
-- impar +1 == sub-fila a=1 de la fila +1 par del mismo nivel?
subrow = (n,q) -> ( (S2,R) := rowIdeal(n,q); m := numgens S2;
  S3 := ZZ/3[x_0..x_(m-2)]; f3 := map(S3, S2, gens S3 | {0_S3});
  (S3, f3(R : x_(m-1))) );
scan({(5,9),(5,27),(7,3)}, nq -> ( (n,q) := nq;
  (S2i, Ri) := rowIdeal(n,q);          -- fila +1 impar, nivel k (n=2k+1)
  (S3, Rs) := subrow(n+1,q);           -- sub-fila 1 de la fila +1 par, nivel k (n+1=2k+2)
  Rs2 := sub(Rs, S2i);
  << "impar n=" << n << " q=" << q << ": r'=" << numColumns basis(S2i/Ri) << " subfila1(par)=" << numColumns basis(S3/Rs) << " igual? " << toString(Rs2 == Ri) << endl << flush;));
<< "FIN-OK" << endl; exit 0
