-- (i) fila generica IMPAR k=2: comprobacion en grado <= 5, independiente de q >= 9
Y = ZZ/3[y_0,y_1,y_2]; e1 = y_0+y_1+y_2; e3 = y_0*y_1*y_2; e2 = y_0*y_1+y_0*y_2+y_1*y_2; P3 = e3 - e1*e2;
L = ideal(P3, e1*e3, e1^3);
<< "impar gen k=2: e1^2 (y1-y2)^2 in (P3,e1e3,e1^3)? " << toString((e1^2*(y_1-y_2)^2) % L == 0) << "   e1^2 y2^3 in? " << toString((e1^2*y_2^3) % L == 0) << "   e1^2 y1^2 in? " << toString((e1^2*y_1^2) % L == 0) << endl;
<< "   dim Y/((L : e1^2) + (e1)) = " << numColumns basis(Y/((L : e1^2) + ideal e1)) << "  (f'_gen(2)=6)" << endl << flush;
-- (ii) identidad "+" con |A|=|B|=2 en J_0 ?
plus2 = (n,q) -> (
  S := ZZ/3[x_0..x_(n-1)]; x := gens S;
  el := j -> sum(subsets(gens S, j), s -> product s);
  J0 := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(x, u -> u^q));
  A := {n-4, n-3}; B := {n-2, n-1}; C := toList(0..n-5);
  xA := product(A, i -> x#i); xB := product(B, i -> x#i); xC := product(C, i -> x#i);
  << "n=" << n << " q=" << q << ": xC(xA^(q-1) + xB^(q-1)) in J0? " << toString((xC*(xA^(q-1) + xB^(q-1))) % J0 == 0)
     << " ; xC(xA^(q-1) - xB^(q-1)) in J0? " << toString((xC*(xA^(q-1) - xB^(q-1))) % J0 == 0)
     << " ; xC xA^(q-1) in J0? " << toString((xC*xA^(q-1)) % J0 == 0) << endl << flush;
  -- y en J1 (colon por la ultima variable): xC xA^(q-1) con C conteniendo... probar xC' xA^(q-1) xB^(q-1)? no. Probar x_c xA^(q-1) in J1 con c fijo:
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  T := ZZ/3[z_0..z_(n)]; elT := j -> sum(subsets(gens T, j), s -> product s);
  IT := ideal(apply(select(toList(1..n+1), j -> odd j), j -> elT j)) + ideal(apply(gens T, u -> u^q));
  g := map(S, T, gens S | {0_S});
  J1 := g(IT : z_n);
  << "     (nivel n+1) xC(xA^(q-1) + xB^(q-1)) in J1? " << toString((xC*(xA^(q-1) + xB^(q-1))) % J1 == 0) << " ; xC xA^(q-1) in J1? " << toString((xC*xA^(q-1)) % J1 == 0) << endl << flush;
);
plus2(5,9); plus2(5,27); plus2(7,3);
<< "FIN-OK" << endl; exit 0
