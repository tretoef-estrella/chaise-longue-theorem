-- ¿R_{q-1} == ∩_{i<j} [(y_i,y_j) + I^{(m-2)}(resto)] ?  (par: m=2k; impar: m=2k-1 con I^{(m-2)} impar)
rowIdeal = (n,q) -> (   -- n = numero de variables del nivel de arriba (2k+2 o 2k+1); devuelve (S2, R_{q-1})
  S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(gens S, u -> u^q));
  S1 := ZZ/3[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := ZZ/3[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  (S2, f2(J1 : (x_(n-2))^(q-1)))
);
test = (n,q) -> (
  (S2, R) := rowIdeal(n,q); m := n-2; y := gens S2;
  oddj := select(toList(1..m-2), j -> odd j);
  Qs := apply(subsets(m,2), ij -> ( rest := select(y, u -> not member(u, {y#(ij#0), y#(ij#1)}));
      ideal(y#(ij#0), y#(ij#1)) + ideal(apply(oddj, j -> sum(subsets(rest, j), s -> product s))) + ideal(apply(y, u -> u^q))));
  Q := intersect Qs;
  << "n=" << n << " q=" << q << " (m=" << m << ")  r_{q-1}=" << numColumns basis(S2/R) << "  dim S/Q=" << numColumns basis(S2/Q) << "  Q==R? " << toString(Q == R) << "  Q⊇R? " << toString(isSubset(R,Q)) << "  R⊇Q? " << toString(isSubset(Q,R)) << endl << flush;
);
test(4,9); test(6,3); test(6,9); test(8,3);     -- par: k=1,2,2,3
test(5,9); test(7,3); test(7,9);                -- impar: k=2,3,3
-- GB de G_4({1,1}) en orden por grado (q=9): levantamientos de los cubicos
q = 9; T = ZZ/3[y_0..y_3, tt]; 
Pt = product(toList(0..3), i -> 1 + y_i*tt) * (1+tt)^2;
R0 = ZZ/3[y_0..y_3, MonomialOrder=>GRevLex];
(Mo, Co) = coefficients(Pt, Variables=>{tt});
Oc = {}; for i from 0 to numColumns Mo - 1 do ( dt := first exponents((flatten entries Mo)_i); if odd(last dt) then Oc = append(Oc, sub(Co_(i,0), R0)) );
G = ideal Oc + ideal(apply(gens R0, u -> u^q - u));
gbG = flatten entries gens gb G;
<< "GB de G_4({1,1}), q=9: " << #gbG << " elementos, grados " << toString apply(gbG, g -> first degree g) << endl;
scan(gbG, g -> if first degree g <= 3 then << "   " << toString g << endl);
<< "FIN-OK" << endl; exit 0
