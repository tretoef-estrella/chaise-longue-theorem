-- (a) certificado y0 y1 y2^(q-1) in Jc (k=2 impar, fila +1), q=9
q = 9; Y = ZZ/3[y_0,y_1,y_2]; y = gens Y;
e1 = y_0+y_1+y_2; e3 = y_0*y_1*y_2; e2 = y_0*y_1+y_0*y_2+y_1*y_2; P3 = e3 - e1*e2;
gensJc = {P3, y_0^q, y_1^q, y_2^q, e1*e3, e1^2*(y_0+y_1)^(q-1), e1^2*(y_0+y_2)^(q-1), e1^2*(y_1+y_2)^(q-1)};
Jc = ideal gensJc;
tgt = y_0*y_1*y_2^(q-1);
<< "y0y1y2^(q-1) in Jc? " << toString(tgt % Jc == 0) << endl;
c = matrix{{tgt}} // matrix{gensJc};
names = {"P3","y0^q","y1^q","y2^q","e1e3","e1^2(y0+y1)^(q-1)","e1^2(y0+y2)^(q-1)","e1^2(y1+y2)^(q-1)"};
scan(#gensJc, i -> if c_(i,0) != 0 then << "   " << names#i << " : " << toString c_(i,0) << endl);
-- minimal subset?
<< "in (P3, box, e1e3)? " << toString(tgt % ideal(P3, y_0^q, y_1^q, y_2^q, e1*e3) == 0) << endl;
<< "in (P3, box, e1^2(y0+y1)^(q-1))? " << toString(tgt % ideal(P3, y_0^q, y_1^q, y_2^q, e1^2*(y_0+y_1)^(q-1)) == 0) << endl;
<< "in (P3, box, e1e3, e1^2(y0+y1)^(q-1))? " << toString(tgt % ideal(P3, y_0^q, y_1^q, y_2^q, e1*e3, e1^2*(y_0+y_1)^(q-1)) == 0) << endl;
-- (b) fila generica impar R'_2, k=2: mingens
rowIdealA = (n,q,a) -> (
  S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  (S2, f2(J1 : (x_(n-2))^a))
);
scan({(5,9,2),(5,27,2),(5,9,1)}, t -> ( (n,q,a) := t; (S2,R) := rowIdealA(n,q,a);
  << "IMPAR k=2 q=" << q << " a=" << a << ": r'=" << numColumns basis(S2/R) << " mingens: " << toString flatten entries mingens R << endl << flush;));
-- (c) fila 1 par = interseccion sobre i de (y_i) + I^{(2k-1)}(resto)?  (curiosidad, filas interiores)
scan({(6,9,1),(8,3,1)}, t -> ( (n,q,a) := t; (S2,R) := rowIdealA(n,q,a); m := numgens S2; yy := gens S2;
  oddj := select(toList(1..m-1), j -> odd j);
  Q := intersect apply(m, i -> ( rest := select(yy, u -> u != yy#i);
       ideal(yy#i) + ideal(apply(oddj, j -> sum(subsets(rest, j), s -> product s))) + ideal(apply(yy, u -> u^q))));
  << "PAR fila 1 n=" << n << " q=" << q << ": r_1=" << numColumns basis(S2/R) << " dim S/Q=" << numColumns basis(S2/Q) << " igual? " << toString(Q==R) << endl << flush;));
<< "FIN-OK" << endl; exit 0
