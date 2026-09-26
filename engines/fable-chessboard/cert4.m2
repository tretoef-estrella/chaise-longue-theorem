c4 = (q) -> (
  R := ZZ/3[x_0..x_4]; x := gens R;
  el := j -> sum(subsets(gens R, j), s -> product s);
  ts := {}; lab := {};
  scan(subsets(5,3), A -> ( lm := toList(set(0..4) - set A);
     ts = append(ts, product(A, i->x#i)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))); lab = append(lab, (A, lm))));
  J := ideal(el 1, el 3, el 5) + ideal apply(x, v->v^q) + ideal ts;
  A := matrix{ts} | matrix{{el 1, el 3, el 5}} | matrix{apply(x, v->v^q)};
  show := (name, tgt) -> (
    << "== q=" << q << " " << name << " in J1cand? " << toString(tgt % J == 0) << endl;
    c := matrix{{tgt}} // A;
    scan(#ts, i -> if c_(i,0) != 0 then << "  t" << toString lab#i << ": " << toString c_(i,0) << endl);
    << "  e1: " << toString c_(#ts,0) << endl << "  e3: " << toString c_(#ts+1,0) << endl << "  e5: " << toString c_(#ts+2,0) << endl;);
  show("U-b: x0 x3^(q-1) x4^(q-1)", x#0*x#3^(q-1)*x#4^(q-1));
  show("G-a: x0^2 x1^(q-2) x4^2", x#0^2*x#1^(q-2)*x#4^2);
  -- also: which sub-generating sets suffice for U-b?
  tgt := x#0*x#3^(q-1)*x#4^(q-1);
  J0 := ideal(el 1, el 3, el 5) + ideal apply(x, v->v^q);
  << "  U-b in J0 + (t with {l,m}={3,4})? " << toString(tgt % (J0 + ideal select(ts, t -> (lab#(position(ts, u->u==t)))#1 == {3,4})) == 0) << endl;
  << "  U-b in J0 + (t with 3,4 in triple)? " << toString(tgt % (J0 + ideal select(#ts, i -> member(3, (lab#i)#0) and member(4, (lab#i)#0)) / (i -> ts#i)) == 0) << endl;
  << "  U-b in J0 + (t with exactly one of 3,4 in pair)? " << toString(tgt % (J0 + ideal (select(#ts, i -> #(set((lab#i)#1) * set{3,4}) == 1) / (i -> ts#i))) == 0) << endl;
  << "  (x0-x1) x3^(q-1) x4^(q-1) in J0 + (x2 x3 x4 (x0^(q-1)-x1^(q-1)))? " << toString(((x#0-x#1)*x#3^(q-1)*x#4^(q-1)) % (J0 + ideal(x#2*x#3*x#4*(x#0^(q-1)-x#1^(q-1)))) == 0) << endl;
  << flush;
);
c4(9);
<< "FIN-OK" << endl; exit 0
