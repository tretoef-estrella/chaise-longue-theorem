cases = {(3,8),(3,9),(5,7),(7,6),(11,3),(11,4),(13,3),(13,4),(9,5)};
scan(cases, c -> (
  q := c#0; n := c#1;
  R := (ZZ/32003)[x_0..x_(n-1)];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  A := R/I;
  hf := apply(toList(0..n*(q-1)), d -> hilbertFunction(d,A));
  while #hf>0 and last hf==0 do hf=drop(hf,-1);
  << "q=" << q << " n=" << n << " HF={" << demark(", ", apply(hf,toString)) << "} total=" << sum hf << endl << flush;
));
