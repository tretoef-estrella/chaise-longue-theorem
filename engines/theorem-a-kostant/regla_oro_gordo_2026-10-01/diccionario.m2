-- (1) char 0: (e_odd)+box == (p_1,p_3,...,p_{q-2})+box as ideals
-- (3) char p odd: ideal of coefficients of E(t)/E(-t)-1 == (e_odd)
scan({(3,4),(5,4),(5,5),(7,4),(7,5),(9,4)}, c -> (
  q := c#0; n := c#1;
  R := QQ[x_0..x_(n-1)];
  box := ideal(apply(gens R, v -> v^q));
  eo := ideal(select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0));
  po := ideal(apply(select(toList(1..q-2), odd), j -> sum(gens R, v -> v^j)));
  << "char0 q=" << q << " n=" << n << " (e_odd)+box == (p_1..p_{q-2} odd)+box : " << ((eo+box) == (po+box)) << endl;
));
scan({(3,4),(3,5),(5,4),(5,6),(7,5)}, c -> (
  p := c#0; n := c#1;
  R := (ZZ/p)[x_0..x_(n-1)];
  S := R[t]/ideal(t^(2*n+2));
  Ep := product(gens R, v -> 1 + t*sub(v,S));
  Em := product(gens R, v -> 1 - t*sub(v,S));
  -- inverse of Em as truncated power series
  inv := 1_S; u := 1 - Em; pw := 1_S;
  for i from 1 to 2*n+1 do ( pw = pw*u; inv = inv + pw; );
  f := Ep*inv - 1;
  cf := apply(toList(1..2*n+1), i -> lift(coefficient(t^i, f), R));
  I1 := ideal select(cf, g -> g != 0);
  eo := ideal(select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), g -> g != 0));
  << "char " << p << " n=" << n << " coeff ideal of E(t)/E(-t)-1 == (e_odd) : " << (I1 == eo) << endl;
));
