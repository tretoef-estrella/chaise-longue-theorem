solve2 = (q) -> (
  R := ZZ/3[a,ap,b,bp]; box := ideal(a^q, ap^q, b^q, bp^q);
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  T := (a*ap)^(q-1) + (b*bp)^(q-1);
  Mat := matrix{{e1*e4, e1*e2 - e3},{e3*e4, e1*e4}};
  Bx := gens box;
  Gen := Mat | (Bx ** id_(R^2));   -- columns: Mat columns and box*(e_1), box*(e_2)
  rhs := matrix{{e1*T},{e3*T}};
  ok := (rhs % Gen == 0);
  << "q=" << q << ": system (I),(II) solvable? " << toString ok << endl;
  if ok then ( c := rhs // Gen; g0 := c_(0,0); g1 := c_(1,0);
     << "  gamma0 = " << toString g0 << endl << "  gamma1 = " << toString g1 << endl;
     << "  check I: " << toString((e1*T - e1*e4*g0 - (e1*e2-e3)*g1) % box == 0) << "  II: " << toString((e3*T - e4*(e1*g1+e3*g0)) % box == 0) << endl;
     -- also try to find a solution with gamma0 = 0
     ok0 := (rhs % (Mat_{1} | (Bx ** id_(R^2))) == 0);
     << "  solvable with gamma0 = 0? " << toString ok0 << endl;
     if ok0 then ( c0 := rhs // (Mat_{1} | (Bx ** id_(R^2))); << "  gamma1 (g0=0) = " << toString c0_(0,0) << endl; );
     ok1 := (rhs % (Mat_{0} | (Bx ** id_(R^2))) == 0);
     << "  solvable with gamma1 = 0? " << toString ok1 << endl;
     if ok1 then ( c1 := rhs // (Mat_{0} | (Bx ** id_(R^2))); << "  gamma0 (g1=0) = " << toString c1_(0,0) << endl; );
  );
  << flush; (R, g0 := if ok then (rhs // Gen)_(0,0) else 0_R, g1 := if ok then (rhs // Gen)_(1,0) else 0_R)
);
-- gate: build the certificate for (k,q) and verify sigma_{2k-3} T == sum c_m e_m mod box in 2k+1 variables
gate = (k,q,g0,g1,R4) -> (
  n := 2*k+1; S := ZZ/3[x_0..x_(n-1)]; x := gens S;
  el := j -> if j<0 then 0_S else if j==0 then 1_S else if j>n then 0_S else sum(subsets(x, j), product);
  Cv := toList(0..n-5); av := x#(n-4); apv := x#(n-3); bv := x#(n-2); bpv := x#(n-1);
  phi := map(S, R4, {av, apv, bv, bpv});
  E := j -> sum(subsets({av,apv,bv,bpv}, j), product);
  e1 := E 1; e2 := E 2; e3 := E 3; e4 := E 4;
  G0 := phi g0; G1 := phi g1; T := (av*apv)^(q-1) + (bv*bpv)^(q-1);
  -- gamma_i by recurrence: (1+e2 t+e4 t^2) Gamma = g0 + (g1+e2 g0) t + T t^2
  gam := new MutableList from {G0, G1};
  gam#2 = T - e2*G1 - e4*G0;
  for i from 3 to k do gam#i = -e2*gam#(i-1) - e4*gam#(i-2);
  cert := sum(toList(0..k), i -> gam#i * el(2*k+1-2*i));
  sig := product(Cv, i -> x#i);
  box := ideal apply(x, v -> v^q);
  << "GATE (k,q)=(" << k << "," << q << "): sigma_{2k-3} T - sum c_m e_m in box? " << toString((sig*T - cert) % box == 0) << endl << flush;
);
(R9, g09, g19) = solve2(9);
(R27, g027, g127) = solve2(27);
gate(3,9,g09,g19,R9); gate(4,3,0_R9,0_R9,R9);
<< "FIN-OK" << endl; exit 0
