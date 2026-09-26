load "m11lib.m2";
-- R3b: which monomials m(y) satisfy z^ell m in K_(1^ell)(n+1) + (z^(ell+2)) ?  (to find a MONOMIAL J for the (T) half)
runB = (q, np1, ell) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  Kp := ideal clK(vs, q, toList(ell:1));
  G := gb(Kp + ideal(z^(ell+2)));
  G1 := gb(Kp + ideal(z^(ell+1)));
  tst := (lab, m) -> << "   " << lab << " : z^l*m in K+(z^(l+2)) " << ((z^ell*m) % G == 0) << " ; z^(l-1)*m in K+(z^l+1)?? " << ((z^(ell-1)*m) % G1 == 0) << endl;
  << "=== q=" << q << " (1^" << ell << ") n+1=" << np1 << endl;
  for k from n-ell-1 to n do tst("squarefree support " | toString k, product take(ys, k));
  c := n - ell - 1;
  if c >= 1 then (
    tst("a*b^(q-1)*x_T |T|=c-1 (A={b},|B|=l)", ys#0 * (ys#1)^(q-1) * product take(drop(ys,2), c-1));
    tst("b^(q-1)*x_T |T|=c (A={b}, |B|=l-1)", (ys#1)^(q-1) * product take(drop(ys,2), c));
    tst("a^2 b^(q-1)*x_T |T|=c-1", (ys#0)^2 * (ys#1)^(q-1) * product take(drop(ys,2), c-1));
  );
  << flush;
);
runB(9,5,2); runB(9,6,2); runB(9,6,3); runB(27,5,2);
<< "FIN-OK" << endl;
