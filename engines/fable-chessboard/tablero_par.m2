-- Conjetura generalizada con DEFICIT c: E_m(c) := coeficientes IMPARES de prod(1+y_i t)*prod_{g in c}(1+g t).
-- ¿La fila R_a (tablero de nivel k) == gr(E_{2k}(c)) + caja, con c = {v, 1}?
cmp = (k,q,a,vc) -> (
  K := if q==3 then ZZ/3 else GF(q, Variable=>w);
  v := if vc==="m" then -1_K else if vc==="z" then 0_K else if vc==="p" then 1_K else (sub(w,K))^vc;
  n := 2*k+2; S := K[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := K[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := K[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  Ra := f2(J1 : (x_(n-2))^a);
  m := 2*k; T := K[x_0..x_(m-1), tt];
  P := product(toList(0..m-1), i -> 1 + x_i*tt) * (1 + v*tt) * (1 + tt);
  D := m+2; R0 := K[x_0..x_(m-1)];
  (Mo, Co) := coefficients(P, Variables=>{tt});
  degs := apply(flatten entries Mo, mo -> (degree mo)_0 - 0);
  Oc := {}; for i from 0 to #degs-1 do ( dt := first exponents((flatten entries Mo)_i); if odd(last dt) then Oc = append(Oc, sub(Co_(i,0), R0)) );
  Ec := ideal Oc;
  Rh := K[x_0..x_(m-1), h]; Eh := homogenize(sub(ideal gens gb Ec, Rh), h);
  grE := sub(Eh, (vars S2) | matrix{{0_S2}}) + ideal(apply(gens S2, u -> u^q));
  Ebox := Ec + ideal(apply(gens R0, u -> u^q - u));
  Ebh := homogenize(sub(ideal gens gb Ebox, Rh), h);
  grEb := sub(Ebh, (vars S2) | matrix{{0_S2}});
  << "(k,q,a)=(" << k << "," << q << "," << a << ") r_a=" << numColumns basis(S2/Ra)
     << " dim/(grE(c)+caja)=" << numColumns basis(S2/grE) << " igual:" << (grE == Ra)
     << " | dim/gr(E(c)+(y^q-y))=" << numColumns basis(S2/grEb) << " igual:" << (grEb == Ra) << endl << flush;
);
cmp(1,3,0,"m"); cmp(1,3,1,"z"); cmp(1,3,2,"p");
cmp(2,3,0,"m"); cmp(2,3,1,"z"); cmp(2,3,2,"p");
cmp(1,9,0,"m"); cmp(1,9,1,"z"); cmp(1,9,2,1); cmp(1,9,8,"p");
cmp(2,9,0,"m"); cmp(2,9,1,"z"); cmp(2,9,2,1); cmp(2,9,8,"p");
<< "FIN-OK" << endl; exit 0
