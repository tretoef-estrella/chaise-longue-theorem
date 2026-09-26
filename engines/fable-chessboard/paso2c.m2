scan({9,27}, q -> (
  Y := ZZ/3[y_0..y_3]; y := gens Y;
  el := j -> sum(subsets(y, j), s -> product s);
  Qgen := intersect apply(subsets(4,2), ij -> ( yi := y#(ij#0); yj := y#(ij#1); rest := select(y, u -> not member(u,{yi,yj}));
     ideal(yi+yj, yi^2, yi*yj, yj^2) + ideal(rest#0 + rest#1) + ideal apply(y, u -> u^q)));
  Ga := ideal(el 1, el 3, el 4) + ideal apply(y, u -> u^q) + ideal flatten apply(4, i -> apply(select(toList(0..3), j -> j != i), j -> y#i^2 * y#j^(q-2)));
  << "k=2 q=" << q << ": Qgen == (e1,e3,e4,caja,x_i^2 x_j^(q-2))? " << toString(Qgen == Ga) << "  dims " << numColumns basis(Y/Qgen) << " " << numColumns basis(Y/Ga) << endl << flush;));
<< "FIN-OK" << endl; exit 0
