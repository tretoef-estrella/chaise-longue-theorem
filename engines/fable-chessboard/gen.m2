rowIdealA = (n,q,a) -> (
  S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  (S2, f2(J1 : (x_(n-2))^a))
);
interGen = (S2,q) -> ( m := numgens S2; y := gens S2;
  oddj := select(toList(1..m-2), j -> odd j);
  intersect apply(subsets(m,2), ij -> ( yi := y#(ij#0); yj := y#(ij#1); rest := select(y, u -> not member(u, {yi,yj}));
      ideal(yi+yj, yi^2, yi*yj, yj^2) + ideal(apply(oddj, j -> sum(subsets(rest, j), s -> product s))) + ideal(apply(y, u -> u^q)))));
scan({(4,9,2),(6,9,2),(6,27,2),(6,9,3),(5,9,2),(7,9,2)}, t -> ( (n,q,a) := t;
  (S2,R) := rowIdealA(n,q,a); Q := interGen(S2,q);
  << "n=" << n << " q=" << q << " a=" << a << ": r_a=" << numColumns basis(S2/R) << " dim S/Qgen=" << numColumns basis(S2/Q) << " Qgen==R? " << toString(Q==R) << " Qgen⊇R? " << toString(isSubset(R,Q)) << " R⊇Qgen? " << toString(isSubset(Q,R)) << endl << flush;));
-- k=2 impar, fila +1: candidato
scan({9,27}, q -> (
  Y := ZZ/3[y_0,y_1,y_2]; y := gens Y;
  e1 := y_0+y_1+y_2; e3 := y_0*y_1*y_2; e2 := y_0*y_1+y_0*y_2+y_1*y_2;
  P3 := e3 - e1*e2;
  Jc := ideal(P3) + ideal apply(y, u -> u^q) + ideal(e1*e3) + ideal apply(subsets(3,2), ij -> e1^2*(y#(ij#0)+y#(ij#1))^(q-1));
  Rc := (Jc : e1^(q-1)) + ideal e1;
  << "k=2 impar q=" << q << ": candidato da dim=" << numColumns basis(Y/Rc) << " (f'_{+1}=3); y0y1 in? " << toString((y_0*y_1) % Rc == 0) << endl << flush;));
<< "FIN-OK" << endl; exit 0
