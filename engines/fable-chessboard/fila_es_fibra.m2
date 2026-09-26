-- ¿R_a (tensor F_q) == gr I(fibra de su clase)? gr = formas tope (homogeneizar y h=0).
fibra = (k,q,a,vc) -> (
  K := if q==3 then ZZ/3 else GF(q, Variable=>w);
  v := if vc==="m" then -1_K else if vc==="z" then 0_K else if vc==="p" then 1_K else (sub(w,K))^vc;
  n := 2*k+2; S := K[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), s -> product s);
  I := ideal(apply(toList(0..k), i -> el(2*i+1))) + ideal(apply(gens S, u -> u^q));
  S1 := K[x_0..x_(n-2)]; f1 := map(S1, S, gens S1 | {0_S1});
  J1 := f1(I : x_(n-1));
  S2 := K[x_0..x_(n-3)]; f2 := map(S2, S1, gens S2 | {0_S2});
  Ra := f2(J1 : (x_(n-2))^a);
  -- puntos de la fibra: y in K^(2k) con {y} u {v, 1} cerrado bajo negacion
  els := if q==3 then {0_K,1_K,-1_K} else unique flatten apply(q, i -> {(sub(w,K))^i}) | {0_K};
  els = unique els;
  cerrado := L -> all(els, e -> #select(L, t -> t==e) == #select(L, t -> t==-e));
  pl := {{}}; for i from 1 to 2*k do pl = flatten apply(pl, p -> apply(els, e -> append(p, e)));
  pts := select(pl, p -> cerrado(p | {v, 1_K}));
  T := K[x_0..x_(n-3), h];
  Ipts := intersect apply(pts, p -> ideal apply(2*k, j -> x_j - p_j));
  gb1 := gens gb Ipts;
  Ih := homogenize(sub(ideal gb1, T), h);
  gr := sub(Ih, (vars S2) | matrix{{0_S2}});
  << "(k,q,a)=(" << k << "," << q << "," << a << ") #fibra=" << #pts << " r_a=" << numColumns basis(S2/Ra)
     << " dim S''/gr=" << numColumns basis(S2/gr) << " gr sub R_a: " << isSubset(gr, Ra) << " R_a == gr: " << (Ra == gr) << endl << flush;
);
fibra(2,3,0,"m");
fibra(1,9,0,"m"); fibra(1,9,1,"z"); fibra(1,9,2,1); fibra(1,9,8,"p");
fibra(2,9,0,"m"); fibra(2,9,1,"z"); fibra(2,9,2,1); fibra(2,9,5,3); fibra(2,9,8,"p");
<< "FIN-OK" << endl; exit 0
