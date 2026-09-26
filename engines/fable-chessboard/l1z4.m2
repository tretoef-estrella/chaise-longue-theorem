-- STEP 1 test: ansatz U = g3*c + g5*c' + a*(b12 b34)^(q-1) + b*[(b13 b24)^(q-1)+(b14 b23)^(q-1)], with Pi*c in box_q
-- Condition: T - a*P0 - b*(P1+P2) in g3*(box_q : Pi) + (eps4) + box_q
for q in {3,9} do (
  R = ZZ/3[x1,x2,x3,x4];
  box = ideal(x1^q,x2^q,x3^q,x4^q);
  e1 = x1+x2+x3+x4; e2 = x1*x2+x1*x3+x1*x4+x2*x3+x2*x4+x3*x4;
  e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
  g3 = e1*e2-e3; Pi = (x1+x2)*(x1+x3)*(x1+x4)*(x2+x3)*(x2+x4)*(x3+x4);
  T = (x1*x2)^(q-1)+(x3*x4)^(q-1);
  P0 = ((x1+x2)*(x3+x4))^(q-1); P1 = ((x1+x3)*(x2+x4))^(q-1); P2 = ((x1+x4)*(x2+x3))^(q-1);
  A = box : Pi;
  << "q=" << q << "  ann(Pi) mingens degrees: " << tally degrees source mingens A << endl;
  J = g3*A + ideal(e4) + box;
  Jold = J;
  << "  adjugate only: T in J? " << (T % J == 0) << endl;
  for a from 0 to 2 do for b from 0 to 2 do (
     f = T - a*P0 - b*(P1+P2);
     if f % J == 0 then << "  SOLUTION a=" << a << " b=" << b << endl;
  );
  Jall = J + ideal(P0,P1,P2);
  << "  T in J + (P0,P1,P2)? " << (T % Jall == 0) << endl;
  -- also: is T in (g3, e4) + box at all (no Pi constraint)? and with planes
  << "  T in (g3,e4)+box? " << (T % (ideal(g3,e4)+box) == 0) << "   T in (g3,e4,P0,P1,P2)+box? " << (T % (ideal(g3,e4,P0,P1,P2)+box) == 0) << endl;
)
