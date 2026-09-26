lemaE = (k,q) -> (
  m := 2*k; R := ZZ/3[x_0..x_(m-1)];
  el := j -> if j==0 then 1_R else if j>m then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el(1);
  P := apply(toList(1..k), i -> el(2*i+1) - e1*el(2*i));   -- P_3, P_5, ...
  box := apply(gens R, v -> v^q);
  K0 := ideal(P | box);
  M := matrix{P | box};
  Z := syz M;   -- columns: syzygies
  -- image: sum_j g_j * e_{j-2}  (j=2i+1 -> e_{2i-1})
  w := matrix{apply(toList(1..k), i -> el(2*i-1))};
  Nmat := w * Z^(toList(0..k-1));
  N := ideal Nmat;
  J1 := K0 + e1*N;
  r := apply(toList(0..q-1), a -> numColumns basis(R/((J1 : e1^a) + ideal e1)));
  << "(k,q)=(" << k << "," << q << ")  LemaE r=" << r << " suma=" << sum r << endl;
  Nmin := trim (N + K0);
  << "  K0+N gens (deg): " << toString apply(flatten entries gens Nmin, g -> first degree g) << endl;
  Nred := select(flatten entries gens Nmin, g -> g % K0 != 0);
  << "  N mod K0 generators: " << endl;
  scan(Nred, g -> << "    deg " << first degree g << ": " << toString g << endl);
  << flush;
);
lemaE(1,9); lemaE(2,3); lemaE(2,9); lemaE(2,27);
<< "FIN-OK" << endl; exit 0
