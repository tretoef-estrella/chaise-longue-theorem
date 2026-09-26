-- Adjugate ansatz for (L1): find c in S_{2q-5} with (i) Pi*c in box_q, (ii) (e3-e1e2)*c == T mod (e4)+box_q.
-- Then gamma1 = -e1*c, U = (e3-e1e2)*c. Cells q=3, q=9 (4 variables, no colon).
for q in {3,9} do (
  R := ZZ/3[a,ap,b,bp]; box := ideal(a^q, ap^q, b^q, bp^q);
  B1 := R/box; 
  e1 := a+ap+b+bp; e2 := a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 := a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 := a*ap*b*bp;
  B2 := R/(box + ideal e4);
  r1 := a*ap; r2 := b*bp; T := r1^(q-1) + r2^(q-1);
  Pi := (a+ap)*(a+b)*(a+bp)*(ap+b)*(ap+bp)*(b+bp);
  mons := flatten entries basis(2*q-5, R);
  m1 := basis(2*q+1, B1); m2 := basis(2*q-2, B2);
  vec := (p1,p2) -> ( (M1,C1) := coefficients(sub(p1,B1), Monomials=>m1); (M2,C2) := coefficients(sub(p2,B2), Monomials=>m2); (sub(C1, ZZ/3)) || (sub(C2, ZZ/3)) );
  cols := apply(mons, m -> vec(Pi*m, (e3-e1*e2)*m));
  A := fold((x,y)->x|y, cols);
  tv := vec(0_R, T);
  sol := tv // A; ok := (A*sol == tv);
  << "q=" << q << " unknowns " << #mons << " rows " << numgens target A << " adjugate ansatz solvable? " << toString ok << endl;
  if ok then ( c := sum(#mons, i -> lift(sol_(i,0),ZZ/3)*mons#i); << "  c (" << #terms c << " terms) = " << toString c << endl;
     -- verify (I),(II) directly
     g1 := -e1*c; U := (e3-e1*e2)*c; 
     << "  check I: " << toString( (sub(e1*U - (e1*e2-e3)*g1, B1)) == 0 ) << endl;
     << "  check II: " << toString( (sub(e3*U - e1*e4*g1, B1)) == 0 ) << endl;
     << "  U-T in (e4)+box: " << toString( sub(U-T, B2) == 0 ) << endl;
     -- kernel dimension of the ansatz system
     << "  kernel dim of ansatz system: " << numgens source syz A << endl;);
  << flush;);
<< "FIN-OK" << endl; exit 0
