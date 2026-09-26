tst = (q) -> (
  R := ZZ/3[x_0..x_3]; x := gens R;
  el := j -> sum(subsets(x, j), product);
  e1 := el 1; P3 := el 3 - e1*el 2; P5 := -e1*el 4;
  box := ideal apply(x, v -> v^q);
  ts := apply(subsets(4,2), ij -> ( lm := toList(set(0..3) - set ij); x#(ij#0)*x#(ij#1)*(x#(lm#0)^(q-1) - x#(lm#1)^(q-1))));
  tgt := e1*x_0^2*x_1^(q-2);
  L := ideal(P3, el 4) + box + ideal(e1^(q-1));
  -- scalar combination of t's mod L? brute force over F_3^6
  found := false;
  for v in toList((set{0,1,2})**(set{0,1,2})**(set{0,1,2})**(set{0,1,2})**(set{0,1,2})**(set{0,1,2})) do (
     cs := toList deepSplice v;
     if (tgt - sum(6, i -> cs#i * ts#i)) % L == 0 then (found = true; << "q=" << q << ": e1 x0^2 x1^(q-2) = sum c_i t_i mod (P3,e4,box,e1^(q-1)) with c = " << toString cs << endl; break;));
  if not found then << "q=" << q << ": NOT a scalar combination of t's mod (P3,e4,box,e1^(q-1))" << endl;
  << "   in (P3,e4,box,e1^(q-1)) + (t's) as ideal? " << toString(tgt % (L + ideal ts) == 0) << endl;
  << "   G-a direct: e1^2 x0^2 x1^(q-2) in (P3,P5,box, e1 t's, e1^3)? " << toString((e1*tgt) % (ideal(P3,P5) + box + ideal apply(ts, t -> e1*t) + ideal(e1^3)) == 0) << endl << flush;
);
tst(9); tst(27);
<< "FIN-OK" << endl; exit 0
