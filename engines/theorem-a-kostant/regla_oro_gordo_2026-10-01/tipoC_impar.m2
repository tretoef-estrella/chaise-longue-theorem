cases = {(2,7),(4,5),(6,3),(6,5),(8,3)};
scan(cases, c -> (
  q := c#0; n := c#1;
  R := (ZZ/32003)[x_0..x_(n-1)];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  hf := apply(toList(0..n*(q-1)), d -> hilbertFunction(d,R/I));
  while #hf>0 and last hf==0 do hf=drop(hf,-1);
  << "q=" << q << " n=" << n << " HF={" << demark(", ", apply(hf,toString)) << "}" << endl << flush;
));
