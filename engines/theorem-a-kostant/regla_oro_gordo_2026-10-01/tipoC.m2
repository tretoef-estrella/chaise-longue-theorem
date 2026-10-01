-- Prediction (Kostant, type C_m): q=2m even, n even: dim QQ[x]/(e_odd, x^q) = # closed loopless walks on Z^m
for c in {(2,2),(2,4),(2,6),(2,8),(4,2),(4,4),(4,6),(6,4),(4,3),(2,3),(2,5)} do (
  q := c#0; n := c#1;
  R := QQ[x_0..x_(n-1)];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  A := R/I;
  hf := apply(toList(0..n*(q-1)), d -> hilbertFunction(d,A));
  while #hf>0 and last hf==0 do hf=drop(hf,-1);
  << "q=" << q << " n=" << n << " HF=" << toString hf << " total=" << sum hf << endl << flush;
);
