cases = {(2,6),(2,8),(4,4),(4,6),(6,4),(4,3),(2,5),(8,4)};
primes = {3,5,7,2};
scan(cases, c -> scan(primes, p -> (
  q := c#0; n := c#1;
  R := (ZZ/p)[x_0..x_(n-1)];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  A := R/I;
  hf := apply(toList(0..n*(q-1)), d -> hilbertFunction(d,A));
  while #hf>0 and last hf==0 do hf=drop(hf,-1);
  << "p=" << p << " q=" << q << " n=" << n << " total=" << sum hf << " HF=" << toString hf << endl << flush;
)));
