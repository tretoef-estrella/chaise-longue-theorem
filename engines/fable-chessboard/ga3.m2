ga = (q) -> (
  R := ZZ/3[x_0..x_3]; x := gens R;
  el := j -> sum(subsets(x, j), product);
  e1 := el 1; P3 := el 3 - e1*el 2; P5 := -e1*el 4;
  bx := apply(x, v -> v^q);
  ts := apply(subsets(4,2), ij -> ( lm := toList(set(0..3) - set ij); e1*x#(ij#0)*x#(ij#1)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))));
  tgt := e1^2*x_0^2*x_1^(q-2);
  full := ideal(P3,P5) + ideal bx + ideal ts + ideal(e1^3);
  << "q=" << q << ": full? " << toString(tgt % full == 0)
     << " | no e1^3? " << toString(tgt % (ideal(P3,P5) + ideal bx + ideal ts) == 0)
     << " | no P3? " << toString(tgt % (ideal(P5) + ideal bx + ideal ts + ideal(e1^3)) == 0)
     << " | no P5? " << toString(tgt % (ideal(P3) + ideal bx + ideal ts + ideal(e1^3)) == 0)
     << " | no t's? " << toString(tgt % (ideal(P3,P5) + ideal bx + ideal(e1^3)) == 0)
     << " | no box? " << toString(tgt % (ideal(P3,P5) + ideal ts + ideal(e1^3)) == 0) << endl;
  -- which t's are needed? try dropping each
  scan(6, i -> << "   drop t" << toString (subsets(4,2))#i << ": " << toString(tgt % (ideal(P3,P5) + ideal bx + ideal drop(ts, {i,i}) + ideal(e1^3)) == 0));
  << endl;
  G := {P3, P5} | bx | ts | {e1^3};
  c := matrix{{tgt}} // matrix{G};
  names := {"P3","P5","x0^q","x1^q","x2^q","x3^q"} | apply(subsets(4,2), ij -> "e1 t"|toString ij) | {"e1^3"};
  scan(#G, i -> if c_(i,0) != 0 then << "   " << names#i << " [" << #terms c_(i,0) << " terms, deg " << toString degree c_(i,0) << "]: " << (if #terms c_(i,0) <= 12 then toString c_(i,0) else "...") << endl);
  << flush;
);
ga(9); ga(27);
<< "FIN-OK" << endl; exit 0
