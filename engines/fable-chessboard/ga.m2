ga = (q, showcert) -> (
  S := ZZ/3[x_0..x_4]; x := gens S;
  el := j -> sum(subsets(gens S, j), s -> product s);
  mons := flatten apply(subsets(5,3), B -> apply(toList(set(0..4) - set B), l -> product(B, i->x#i) * x#l^(q-1)));
  Jc2 := ideal(el 1, el 3, el 5) + ideal apply(x, v->v^q) + ideal mons;
  -- true J1
  T := ZZ/3[y_0..y_5]; el6 := j -> sum(subsets(gens T, j), s -> product s);
  I := ideal(el6 1, el6 3, el6 5) + ideal apply(gens T, v -> v^q);
  f1 := map(S, T, gens S | {0_S});
  J1 := f1(I : y_5);
  << "== q=" << q << "  J1 == Jc2? " << toString(J1 == Jc2) << "   Jc2 ⊆ J1? " << toString(isSubset(Jc2, J1)) << endl;
  tgt := x#4^2 * x#0^2 * x#1^(q-2);
  << "  G-a: x4^2 x0^2 x1^(q-2) in Jc2 + (x4^3)? " << toString(tgt % (Jc2 + ideal(x#4^3)) == 0) << endl;
  if showcert then (
    A := matrix{mons} | matrix{{el 1, el 3, el 5, x#4^3}} | matrix{apply(x, v->v^q)};
    c := matrix{{tgt}} // A;
    scan(#mons, i -> if c_(i,0) != 0 then << "   " << toString mons#i << " : " << toString c_(i,0) << endl);
    << "   e1 : " << toString c_(#mons,0) << endl;
    << "   e3 : " << toString c_(#mons+1,0) << endl;
    << "   e5 : " << toString c_(#mons+2,0) << endl;
    << "   x4^3 : " << toString c_(#mons+3,0) << endl;);
  << flush;
);
ga(9, true); ga(27, false);
<< "FIN-OK" << endl; exit 0
