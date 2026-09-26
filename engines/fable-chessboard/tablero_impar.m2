-- Nivel IMPAR: 2k+1 letras, I' = e_impar + caja; J'_1 = pi(I' : y_{2k}); filas R'_a = pi(J'_1 : y_{2k-1}^a).
-- ¿R'_a == gr(E_{2k-1}(c) + (y^q - y)) con c = {v,1}?
cmpi = (k,q,a,vc) -> (
  K := if q==3 then ZZ/3 else GF(q, Variable=>w);
  v := if vc==="m" then -1_K else if vc==="z" then 0_K else if vc==="p" then 1_K else (sub(w,K))^vc;
  n := 2*k+1; S := K[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := K[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := K[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  Ra := f2(J1 : (x_(n-2))^a);
  m := n-2; R0 := K[x_0..x_(m-1)]; T := K[x_0..x_(m-1), tt];
  P := product(toList(0..m-1), i -> 1 + x_i*tt) * (1 + v*tt) * (1 + tt);
  (Mo, Co) := coefficients(P, Variables=>{tt});
  Oc := {}; for i from 0 to numColumns Mo - 1 do ( dt := first exponents((flatten entries Mo)_i); if odd(last dt) then Oc = append(Oc, sub(Co_(i,0), R0)) );
  G := ideal Oc + ideal(apply(gens R0, u -> u^q - u));
  Rh := K[x_0..x_(m-1), h]; Gh := homogenize(sub(ideal gens gb G, Rh), h);
  grG := sub(Gh, (vars S2) | matrix{{0_S2}});
  << "IMPAR (k,q,a)=(" << k << "," << q << "," << a << ") r'_a=" << numColumns basis(S2/Ra) << " |fibra|=" << numColumns basis(S2/grG) << " igual:" << (grG == Ra) << endl << flush;
);
cmpi(1,3,0,"m"); cmpi(1,3,1,"z"); cmpi(1,3,2,"p");
cmpi(2,3,0,"m"); cmpi(2,3,1,"z"); cmpi(2,3,2,"p");
cmpi(1,9,0,"m"); cmpi(1,9,1,"z"); cmpi(1,9,2,1); cmpi(1,9,8,"p");
cmpi(2,9,0,"m"); cmpi(2,9,1,"z"); cmpi(2,9,2,1); cmpi(2,9,8,"p");
cmpi(3,3,0,"m"); cmpi(3,3,1,"z"); cmpi(3,3,2,"p");
<< "FIN-OK" << endl; exit 0
