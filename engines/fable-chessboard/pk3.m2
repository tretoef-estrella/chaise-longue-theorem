solveNF = (q) -> (
  R := ZZ/3[a,ap,b,bp, MonomialOrder=>GRevLex]; box := ideal(a^q, ap^q, b^q, bp^q);
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  T := (a*ap)^(q-1) + (b*bp)^(q-1);
  Mat := matrix{{e1*e4, e1*e2 - e3},{e3*e4, e1*e4}};
  Gen := Mat | (gens box ** id_(R^2));
  rhs := matrix{{e1*T},{e3*T}};
  c := rhs // Gen; g := matrix{{c_(0,0)},{c_(1,0)}};
  -- homogeneous solutions: (g0,g1) with Mat*g in box*R^2  <=> first two rows of syz(Gen)
  Z := syz Gen; H := image(Z^{0,1});
  gnf := g % (gb H);
  << "q=" << q << ": normal form gamma0 = " << toString gnf_(0,0) << endl << "        gamma1 = " << toString gnf_(1,0) << endl;
  << "   #terms " << #terms gnf_(0,0) << ", " << #terms gnf_(1,0) << "  degrees " << toString degree gnf_(0,0) << toString degree gnf_(1,0) << endl << flush;
  (R, gnf_(0,0), gnf_(1,0))
);
gate = (k,q,g0,g1,R4) -> (
  n := 2*k+1; S := ZZ/3[x_0..x_(n-1)]; x := gens S;
  el := j -> if j<0 then 0_S else if j==0 then 1_S else if j>n then 0_S else sum(subsets(x, j), product);
  Cv := toList(0..n-5); av := x#(n-4); apv := x#(n-3); bv := x#(n-2); bpv := x#(n-1);
  phi := map(S, R4, {av, apv, bv, bpv});
  E := j -> sum(subsets({av,apv,bv,bpv}, j), product);
  e2 := E 2; e4 := E 4;
  G0 := phi g0; G1 := phi g1; T := (av*apv)^(q-1) + (bv*bpv)^(q-1);
  gam := new MutableList from {G0, G1}; gam#2 = T - e2*G1 - e4*G0;
  for i from 3 to k do gam#i = -e2*gam#(i-1) - e4*gam#(i-2);
  cert := sum(toList(0..k), i -> gam#i * el(2*k+1-2*i));
  sig := product(Cv, i -> x#i); box := ideal apply(x, v -> v^q);
  << "GATE (k,q)=(" << k << "," << q << "): certificate exact mod box? " << toString((sig*T - cert) % box == 0) << endl << flush;
);
(R3,a3,b3) = solveNF(3); gate(3,3,a3,b3,R3); gate(4,3,a3,b3,R3);
(R9,a9,b9) = solveNF(9); gate(3,9,a9,b9,R9);
(R27,a27,b27) = solveNF(27);
<< "FIN-OK" << endl; exit 0
