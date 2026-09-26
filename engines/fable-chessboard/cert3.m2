c3 = (q) -> (
  R := ZZ/3[x_0..x_4]; x := gens R;
  el := j -> sum(subsets(gens R, j), s -> product s);
  ts := {}; lab := {};
  scan(subsets(5,3), A -> ( lm := toList(set(0..4) - set A);
     ts = append(ts, product(A, i->x#i)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))); lab = append(lab, (A, lm))));
  J := ideal(el 1, el 3, el 5) + ideal apply(x, v->v^q) + ideal ts;
  tgt := x#0*x#1*x#2*x#3^(q-1);
  << "== q=" << q << " x0x1x2x3^(q-1) in J1cand(5 vars)? " << toString(tgt % J == 0) << endl;
  A := matrix{ts} | matrix{{el 1, el 3, el 5}} | matrix{apply(x, v->v^q)};
  c := matrix{{tgt}} // A;
  scan(#ts, i -> if c_(i,0) != 0 then << "  t" << toString lab#i << ": " << toString c_(i,0) << endl);
  << "  e1: " << toString c_(#ts,0) << endl << "  e3: " << toString c_(#ts+1,0) << endl << "  e5: " << toString c_(#ts+2,0) << endl;
  << flush;
);
c3(9);
<< "FIN-OK" << endl; exit 0
