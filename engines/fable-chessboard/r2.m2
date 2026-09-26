load "m11lib.m2";
-- R2: row 0 = substitution z=0.  pi(K_mu(n+1)) contains K_{mu - e_1}(n)?  (and: does the layer come out?)
lowerFirst = mu -> ( nu := {mu#0 - 1} | drop(mu, 1); nu = rsort select(nu, x -> x > 0); nu );
runR2 = (q, np1, mu) -> (
  n := np1 - 1; T := ZZ/3[y_1..y_n, z, MonomialOrder=>GRevLex]; ys := toList(y_1..y_n); vs := ys | {z};
  nu := lowerFirst mu;
  Kp := clK(vs, q, mu);
  pz := map(T, T, ys | {0_T});
  R0 := ideal apply(Kp, g -> pz g) + ideal(z);
  G := gb R0;
  Kc := if #nu == 0 then clK(ys, q, {}) else clK(ys, q, nu);
  bad := select(Kc, g -> g % G != 0);
  << "q=" << q << " parent " << toString mu << " n+1=" << np1 << " -> child " << toString nu << " n=" << n << " : child in pi(K_parent)? " << (#bad == 0) << " (" << #bad << " missing gens)" << endl << flush;
  if #bad > 0 then << "     first missing: " << toString take(bad, 3) << endl << flush;
);
for mu in {{1,1},{2,1},{3,1},{2,2},{1,1,1},{2,1,1},{1,1,1,1},{3,2},{2,2,1},{3,1,1},{4,1}} do
  for np1 from sum mu + 1 to 6 do runR2(9, np1, mu);
runR2(27,5,{1,1}); runR2(27,5,{2,1}); runR2(27,5,{1,1,1}); runR2(27,5,{2,2});
<< "FIN-OK" << endl;
