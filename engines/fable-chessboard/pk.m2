-- (P_k) reduced to a k-independent system in F_3[a,a',b,b']:
--  find d, d' with (i) r1 r2 d in box, (ii) (b1 r2 + b2 r1) d in box, (iii) e2 d + r1 r2 d' == r1^(q-1)+r2^(q-1) mod box
test = (q) -> (
  R := ZZ/3[a,ap,b,bp]; box := ideal(a^q, ap^q, b^q, bp^q);
  r1 := a*ap; r2 := b*bp; b1 := a+ap; b2 := b+bp; e2 := r1 + r2 + b1*b2;
  T := r1^(q-1) + r2^(q-1);
  D := (box : (r1*r2)) * 1_R; D = intersect(box : (r1*r2), box : (b1*r2 + b2*r1));
  << "q=" << q << ": T in e2*D + (r1 r2) + box? " << toString(T % (e2*D + ideal(r1*r2) + box) == 0) << endl;
  << "   T in e2*D + box (d' = 0)? " << toString(T % (e2*D + box) == 0) << endl;
  << "   T in (e2, r1 r2) + box? " << toString(T % (ideal(e2, r1*r2) + box) == 0) << endl;
  << "   gens D (degrees): " << toString apply(flatten entries mingens D, g -> first degree g) << endl;
  -- extract a certificate if possible: write T = e2*d + r1 r2 d' + box with d in D
  if T % (e2*D + ideal(r1*r2) + box) == 0 then (
     Dg := flatten entries mingens D;
     A := matrix{apply(Dg, g -> e2*g)} | matrix{{r1*r2}} | gens box;
     c := matrix{{T}} // A;
     d := sum(#Dg, i -> c_(i,0) * Dg#i); dp := c_(#Dg,0);
     << "   d  = " << toString d << endl << "   d' = " << toString dp << endl;
     << "   check (i) " << toString((r1*r2*d) % box == 0) << " (ii) " << toString(((b1*r2+b2*r1)*d) % box == 0) << " (iii) " << toString((e2*d + r1*r2*dp - T) % box == 0) << endl;);
  << flush;
);
test(9); test(27);
<< "FIN-OK" << endl; exit 0
