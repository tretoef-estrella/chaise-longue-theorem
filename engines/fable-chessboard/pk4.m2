-- symmetric ansatz: gamma0, gamma1 in F_3[b1,b2,r1,r2] (weights 1,1,2,2), degrees 2q-6, 2q-4; solve (I),(II) mod box by linear algebra over F_3
sym = (q) -> (
  R := ZZ/3[a,ap,b,bp]; box := ideal(a^q, ap^q, b^q, bp^q); B := R/box;
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  T := (a*ap)^(q-1) + (b*bp)^(q-1);
  b1 := a+ap; b2 := b+bp; r1 := a*ap; r2 := b*bp;
  wmons := d -> flatten flatten flatten apply(toList(0..d), i -> apply(toList(0..d-i), j -> apply(toList(0..(d-i-j)//2), kk -> if (d-i-j-2*kk) % 2 == 0 then {(i,j,kk,(d-i-j-2*kk)//2)} else {})));
  mon := (i,j,kk,l) -> b1^i*b2^j*r1^kk*r2^l;
  L0 := wmons(2*q-6); L1 := wmons(2*q-4);
  cols := apply(L0, t -> (sub(e1*e4*mon t, B), sub(e3*e4*mon t, B))) | apply(L1, t -> (sub((e1*e2-e3)*mon t, B), sub(e1*e4*mon t, B)));
  tgt := (sub(e1*T, B), sub(e3*T, B));
  -- coefficient vectors w.r.t. monomial bases of B in degrees 2q-1 and 2q+1
  m1 := basis(2*q-1, B); m2 := basis(2*q+1, B);
  vec := p -> ( (M1,C1) := coefficients(p#0, Monomials=>m1); (M2,C2) := coefficients(p#1, Monomials=>m2); (C1 || C2) );
  A := fold((x,y) -> x | y, apply(cols, vec));
  tv := vec tgt;
  A3 := sub(A, ZZ/3); t3 := sub(tv, ZZ/3);
  sol := t3 // A3;
  ok := (A3 * sol == t3);
  << "q=" << q << ": symmetric ansatz solvable? " << toString ok << "  (#basis " << #L0 << "+" << #L1 << ")" << endl;
  if ok then (
     n0 := #L0;
     g0 := sum(n0, i -> sub(sol_(i,0), ZZ/3) * mon L0#i); g1 := sum(#L1, i -> sub(sol_(n0+i,0), ZZ/3) * mon L1#i);
     -- print in terms of b1,b2,r1,r2
     W := ZZ/3[B1,B2,R1,R2, Degrees=>{1,1,2,2}];
     g0w := sum(n0, i -> lift(sol_(i,0), ZZ/3) * (B1^(L0#i#0)*B2^(L0#i#1)*R1^(L0#i#2)*R2^(L0#i#3)));
     g1w := sum(#L1, i -> lift(sol_(n0+i,0), ZZ/3) * (B1^(L1#i#0)*B2^(L1#i#1)*R1^(L1#i#2)*R2^(L1#i#3)));
     << "  gamma0 = " << toString g0w << endl << "  gamma1 = " << toString g1w << endl;
     << "  check I,II in R: " << toString((e1*T - e1*e4*g0 - (e1*e2-e3)*g1) % box == 0) << " " << toString((e3*T - e4*(e1*g1+e3*g0)) % box == 0) << endl;);
  << flush;
);
sym(3); sym(9); sym(27);
<< "FIN-OK" << endl; exit 0
