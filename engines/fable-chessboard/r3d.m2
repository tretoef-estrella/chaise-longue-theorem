load "m11lib.m2";
-- R3d: is the closed-form T in J_ell (full ideal, polynomial multipliers)?  ell = 3 is the test (1/ell fails in char 3)
Hh = (D, u, b, q) -> sum apply(toList(1..D-1), i -> if i <= q-1 and D-i <= q-1 then u^i * b^(D-i) else 0);
runD = (q, np1, ell) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S; a := ys#0; b := ys#1; u := -a;
  c := n - ell - 1; N := q + c - 2; R := c // 2;
  t0 := cpuTime();
  T := sum apply(toList(0..R), r -> (-1)^c * Hh(N - 2*r, u, b, q) * clE(ys, 2*r+1));
  Jg := apply(ys, v -> v^q) | apply(select(toList(1..n), k -> k >= n-ell+1), k -> clE(ys,k));
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then Jg = append(Jg, clPhi(ys, q, ell, n-2, j, l));
  Jphi := apply(toList(0..n-1), j -> (ys#j)^(q-ell) * sum apply(toList(0..ell-1), i -> (ys#j)^i * clE(drop(ys,{j,j}), n-1-i)));
  G1 := gb ideal Jg; G2 := gb ideal(Jg | Jphi);
  << "q=" << q << " (1^" << ell << ") n+1=" << np1 << " c=" << c << " : T in box+e_{>=c+2}+F^(l)(n)? " << (T % G1 == 0) << " ; with phi_{j,z} too? " << (T % G2 == 0) << " [" << cpuTime()-t0 << "s]" << endl << flush;
);
runD(9,7,3); runD(27,6,3); runD(9,7,2); runD(27,6,2);
<< "FIN-OK" << endl;
