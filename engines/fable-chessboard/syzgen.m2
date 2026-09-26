chk = (k,q) -> (
  m := 2*k; R := ZZ/3[x_0..x_(m-1)]; x := gens R;
  el := j -> if j==0 then 1_R else if j>m then 0_R else sum(subsets(gens R, j), s -> product s);
  e1 := el 1;
  P := apply(toList(1..k), i -> el(2*i+1) - e1*el(2*i));   -- P_3..P_{2k+1}
  box := ideal apply(x, v -> v^q);
  l := 0; mm := 1; A := toList(2..m-1);
  w := sum(toList(0..q-2), s -> (-1)^s * x#l^(q-2-s) * x#mm^s);
  r := x#l * x#mm;
  -- g_{2k+1-2s} = w (-r)^s, i.e. g for P_{2i+1} (i=1..k) is w(-r)^(k-i)
  g := apply(toList(1..k), i -> w * (-r)^(k-i));
  syzOK := (sum(k, i -> g#i * P#i)) % box == 0;
  img := sum(k, i -> g#i * el(2*i+1));
  t := product(A, a -> x#a) * (x#l^(q-1) - x#mm^(q-1));
  << "(k,q)=(" << k << "," << q << ")  syzygy in box? " << toString syzOK << "   image == t mod box? " << toString((img - t) % box == 0) << endl;
);
chk(1,9); chk(2,9); chk(2,27); chk(3,3);
<< "FIN-OK" << endl; exit 0
