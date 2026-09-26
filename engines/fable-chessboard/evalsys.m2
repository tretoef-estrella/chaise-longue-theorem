-- Is the evaluation system (C_i): prod_{j!=i}(x_i+x_j) * (U - gamma1*x_i*sigma1^(i)) == 0 mod box_q (i=1..4), U = T - e4*gamma0,
-- equivalent to (L1)? Compare row spaces of the two linear systems in the unknowns (gamma0 in deg 2q-6, gamma1 in deg 2q-4).
for q in {3,9} do (
  R := ZZ/3[a,ap,b,bp]; X := {a,ap,b,bp}; box := ideal(a^q, ap^q, b^q, bp^q); B := R/box;
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  r1 := a*ap; r2 := b*bp; T := r1^(q-1) + r2^(q-1);
  mons0 := flatten entries basis(2*q-6, R); mons1 := flatten entries basis(2*q-4, R);
  mL := basis(2*q-1, B); mL2 := basis(2*q+1, B);
  vecL := (p1,p2) -> ( (M1,C1) := coefficients(sub(p1,B), Monomials=>mL); (M2,C2) := coefficients(sub(p2,B), Monomials=>mL2); (sub(C1,ZZ/3)) || (sub(C2,ZZ/3)) );
  -- (I): e1*(T - e4 g0) - (e1e2-e3) g1 = 0 ; (II): e3*(T - e4 g0) - e1 e4 g1 = 0
  colsL := apply(mons0, m -> vecL(-e1*e4*m, -e3*e4*m)) | apply(mons1, m -> vecL(-(e1*e2-e3)*m, -e1*e4*m));
  AL := fold((x,y)->x|y, colsL); tL := vecL(-e1*T, -e3*T);   -- AL*sol = tL  <=> AL*sol - tL = 0 ... sign: cols carry unknown part, target = -(constant part)
  -- (C_i)
  mC := basis(2*q+1, B);
  vecC := p -> ( (M,C) := coefficients(sub(p,B), Monomials=>mC); sub(C,ZZ/3) );
  Pi := i -> product(select(X, y -> y =!= X#i), y -> X#i + y);
  sig := i -> e1 - X#i;
  rowsC := apply(4, i -> ( PP := Pi i;
     A := fold((x,y)->x|y, apply(mons0, m -> vecC(-PP*e4*m)) | apply(mons1, m -> vecC(-PP*(X#i)*(sig i)*m)));
     t := vecC(-PP*T); (A,t)));
  AC := fold((x,y)->x||y, apply(rowsC, p -> p#0)); tC := fold((x,y)->x||y, apply(rowsC, p -> p#1));
  rL := rank AL; rC := rank AC; rLC := rank (AL || AC);
  << "q=" << q << " unknowns " << #mons0+#mons1 << " rank(L1)=" << rL << " rank(C)=" << rC << " rank(L1|C)=" << rLC << endl;
  << "  (C) implies (L1)? " << toString(rC == rLC) << "   (L1) implies (C)? " << toString(rL == rLC) << endl;
  solC := tC // AC; << "  (C) solvable? " << toString(AC*solC == tC) << endl;
  solL := tL // AL; << "  (L1) solvable? " << toString(AL*solL == tL) << "  kernel dim L1 = " << (#mons0+#mons1 - rL) << endl;
  << flush;);
<< "FIN-OK" << endl; exit 0
