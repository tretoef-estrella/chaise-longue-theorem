load "m11lib.m2";
-- R5: raise row q-ell of (1^ell)(n+1) -> (2,1^(ell-1))(n).  Known-in-row pieces: R_{ell+1} ⊇ K_(1^(ell+1))(n) (proved), Pi(y\b) (from phi_{z,l}),
-- child family = X' - a^(q-l-1) Pi P.  Does  Known := K_(1^(l+1))(n) + (Pi(y\b)) + box  contain the whole child K_(2,1^(l-1))(n)?  which gens fail?
runE = (q, np1, ell) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  known := clK(ys, q, toList((ell+1):1)) | apply(ys, b -> product delete(b, ys));
  Gk := gb ideal known;
  nu := {2} | toList((ell-1):1);
  Kc := clK(ys, q, nu);
  bad := select(Kc, g -> g % Gk != 0);
  << "q=" << q << " (1^" << ell << ") n+1=" << np1 << " raise child " << toString nu << " n=" << n << " : child gens not in Known: " << #bad << " of " << #Kc << endl;
  if #bad > 0 then << "    e.g. " << toString take(bad, 4) << endl;
  -- true row test: child in R_{q-ell}(K_parent)?
  Kp := ideal clK(vs, q, toList(ell:1));
  G := gb(Kp + ideal(z^(q-ell+1)));
  okr := all(Kc, g -> (z^(q-ell)*g) % G == 0);
  << "   whole child in row q-ell of the parent (membership): " << okr << " ; bad gens in row q-ell: " << toString apply(bad, g -> (z^(q-ell)*g) % G == 0) << endl << flush;
);
runE(9,5,1); runE(9,5,2); runE(9,6,2); runE(9,6,3); runE(27,5,2);
<< "FIN-OK" << endl;
