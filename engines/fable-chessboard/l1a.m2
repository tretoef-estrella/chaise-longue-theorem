-- ansatz: gamma0 = e1^(q-3) * rho(r1,r2), rho of r-degree (q-3)/2 ; gamma1 free. Solve over F_3 for the coefficients of rho.
ans = (q) -> (
  R := ZZ/3[a,ap,b,bp]; box := ideal(a^q, ap^q, b^q, bp^q);
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  r1 := a*ap; r2 := b*bp; T := r1^(q-1) + r2^(q-1);
  col1 := matrix{{e1*e2 - e3},{e1*e4}};          -- gamma1 column
  Gen := col1 | (gens box ** id_(R^2));
  Q := R^2 / image Gen;
  rhs := matrix{{e1*T},{e3*T}};
  d := (q-3)//2;
  cands := apply(toList(0..d), i -> ( g0 := e1^(q-3) * r1^i * r2^(d-i); matrix{{e1*e4*g0},{e3*e4*g0}} ));
  -- normal forms in Q
  nf := v -> (map(Q, R^1, v))_(0) ;   -- element of Q
  -- linear algebra: find c with rhs = sum c_i cands_i in Q  <=> rhs - sum c_i cands_i in image Gen
  found := false;
  combos := toList(fold((x,y) -> x ** y, apply(d+1, i -> set{0,1,2})));
  for v in combos do ( cs := if d == 0 then {v} else toList deepSplice v;
     w := rhs - sum(d+1, i -> cs#i * cands#i);
     if w % Gen == 0 then (found = true; << "q=" << q << ": ansatz gamma0 = e1^(q-3)*rho works with rho coefficients (r1^i r2^(d-i), i=0..d) = " << toString cs << endl; break;));
  if not found then << "q=" << q << ": ansatz gamma0 = e1^(q-3)*rho(r1,r2) FAILS" << endl;
  << flush;
);
ans(3); ans(9);
<< "FIN-OK" << endl; exit 0
