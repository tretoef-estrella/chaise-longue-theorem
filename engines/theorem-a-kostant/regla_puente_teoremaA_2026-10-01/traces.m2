-- graded traces of S_n on A = QQ[x]/(e_odd, x_i^q), one representative per cycle type
cases = {(3,2),(3,3),(3,4),(3,5),(3,6),(5,2),(5,3),(5,4),(5,5),(5,6)};
cycPerm = (lam, n) -> ( -- permutation as list sigma(i), 0-based
    p := new MutableList from toList(0..n-1); start := 0;
    for c in lam do ( for j from 0 to c-1 do p#(start+j) = start + ((j+1)%c); start = start + c; );
    toList p );
scan(cases, c -> (
  q := c#0; n := c#1;
  R := QQ[x_0..x_(n-1)];
  gs := select(apply(toList(1..n), j -> if odd j then sum(subsets(gens R, j), s->product s) else 0_R), f -> f != 0);
  I := ideal(gs) + ideal(apply(gens R, v -> v^q));
  G := gb I;
  top := n*(q-1);
  for lam in partitions n do (
     sig := cycPerm(toList lam, n);
     phi := map(R, R, apply(n, i -> x_(sig#i)));
     tr := for d from 0 to top list (
        B := flatten entries basis(d, R/I);
        if #B == 0 then 0 else (
          Bl := apply(B, b -> lift(b, R));
          sum apply(Bl, b -> coefficient(b, (phi b) % G)) ) );
     while #tr > 0 and last tr == 0 do tr = drop(tr,-1);
     << "q=" << q << " n=" << n << " lam=" << toString toList lam << " tr=" << toString tr << endl;
  );
));
