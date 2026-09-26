-- check: gr G_{2k+1}({1}) (= gr I(V_1)) is contained in J_1 = pi(I^(2k+2) : x_{2k+1}), cells (1,9), (2,9)
chk = (k,q) -> (
  K := GF(q, Variable=>w); n := 2*k+2; S := K[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), product);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := K[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  m := n-1; R0 := K[y_0..y_(m-1)]; T := K[y_0..y_(m-1), tt];
  P := product(toList(0..m-1), i -> 1 + y_i*tt) * (1 + tt);
  (Mo, Co) := coefficients(P, Variables=>{tt});
  Oc := {}; for i from 0 to numColumns Mo - 1 do ( dt := first exponents((flatten entries Mo)_i); if odd(last dt) then Oc = append(Oc, sub(Co_(i,0), R0)) );
  G := ideal Oc + ideal(apply(gens R0, u -> u^q - u));
  Rh := K[y_0..y_(m-1), h]; Gh := homogenize(sub(ideal gens gb G, Rh), h);
  grG := sub(Gh, (vars S1) | matrix{{0_S1}});
  << "(k,q)=(" << k << "," << q << "): dim S/J1=" << numColumns basis(S1/J1) << " dim S/grI(V1)=" << numColumns basis(S1/grG) << "  grI(V1) ⊆ J1? " << toString(isSubset(grG, J1)) << "  equal? " << toString(grG == J1) << endl << flush;
);
chk(1,9); chk(2,9);
<< "FIN-OK" << endl; exit 0
