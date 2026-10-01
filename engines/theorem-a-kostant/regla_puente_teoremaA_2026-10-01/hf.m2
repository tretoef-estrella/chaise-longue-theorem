cases = {(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(5,2),(5,3),(5,4),(5,5),(5,6),(7,2),(7,3),(7,4),(7,5)};
scan(cases, c -> (
  q := c#0; n := c#1;
  R := ZZ/101[x_1..x_n];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  p := apply(toList(0..(n*(q-1))), d -> hilbertFunction(d, R/I));
  while #p > 0 and last p == 0 do p = drop(p,-1);
  << "q=" << q << " n=" << n << " HF=" << toString p << " total=" << sum p << endl;
));
