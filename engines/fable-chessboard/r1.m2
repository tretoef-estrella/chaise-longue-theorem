load "m11lib.m2";
-- R1: VZ_ell for (1^ell): z^ell * phi_child in K_parent exactly; and child K subset of row ell; row ell-1 does not contain the family
runR1 = (q, np1, ell) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  mu := toList(ell:1);
  t0 := cpuTime();
  Kp := ideal clK(vs, q, mu); G := gb Kp;
  -- (a) exact certificate of 0.1
  ok1 := true;
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then (
    ph := clPhi(ys, q, ell, n-2, j, l);
    if (z^ell * ph) % G != 0 then ok1 = false);
  -- (b) the one-line certificate itself
  ok2 := true;
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then (
    php := clPhi(vs, q, ell, n-1, j, l); ph := clPhi(ys, q, ell, n-2, j, l);
    mult := sum apply(toList(0..ell-1), i -> z^(ell-1-i) * (-ys#j)^i);
    diff0 := z^ell * ph - mult * php;
    if diff0 % gb ideal apply(vs, v -> v^q) != 0 then ok2 = false);
  -- (c) whole child in row ell (membership z^ell g in K + z^(ell+1)); row ell-1 misses the family
  Ga := gb(Kp + ideal(z^(ell+1)));
  Kc := clK(ys, q, mu);
  ok3 := all(Kc, g -> (z^ell * g) % Ga == 0);
  Gb := gb(Kp + ideal(z^ell));
  ph0 := clPhi(ys, q, ell, n-2, 0, 1);
  ok4 := (z^(ell-1) * ph0) % Gb != 0;
  << "q=" << q << " parent (1^" << ell << ") n+1=" << np1 << " : z^l*phi_c in K exactly: " << ok1 << " ; one-line certificate mod box: " << ok2
     << " ; whole child K_(1^l)(n) in row l: " << ok3 << " ; family NOT in row l-1: " << ok4 << " [" << cpuTime()-t0 << "s]" << endl << flush;
);
runR1(9,5,2); runR1(9,5,3); runR1(9,5,4);
runR1(9,6,2); runR1(9,6,3); runR1(9,6,4);
runR1(27,5,2); runR1(27,5,3);
<< "FIN-OK" << endl;
