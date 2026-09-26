-- G-a in the eliminated 4-variable form (z = -eps1). Check the reduction and get a lift at q = 9, 27.
for q in {9,27} do (
  R = ZZ/3[x0,x1,x2,x3]; xs = {x0,x1,x2,x3};
  box = ideal apply(xs, x -> x^q);
  E1 = sum xs;
  E2 = sum flatten for i from 0 to 3 list for j from i+1 to 3 list xs#i*xs#j;
  E3 = sum flatten flatten for i from 0 to 3 list for j from i+1 to 3 list for k from j+1 to 3 list xs#i*xs#j*xs#k;
  E4 = x0*x1*x2*x3;
  g3 = E1*E2 - E3; g5 = E1*E4;
  monA = ideal apply(xs, x -> E4*x^(q-2));
  monB = ideal flatten flatten for c from 0 to 3 list for a from 0 to 3 list for a2 from a+1 to 3 list (if c != a and c != a2 then xs#c*(xs#a*xs#a2)^(q-1) else 0_R);
  cross = ideal flatten flatten for a from 0 to 3 list for i from 0 to 3 list for i2 from i+1 to 3 list (if i != a and i2 != a then (xs#i+xs#i2)*xs#i*xs#i2*xs#a^(q-1) else 0_R);
  KK = ideal(g3, g5, E1^3) + cross + monA + monB + box;
  tgt = E1^2*x0^2*x1^(q-2);
  Pp = (x1+x2)*(x1+x3)*(x2+x3); e2p = x1*x2+x1*x3+x2*x3;
  << "q=" << q << "  G-a (eliminated): " << (tgt % KK == 0) << "   E1*Pi'*x1^(q-2) in KK: " << ((E1*Pp*x1^(q-2)) % KK == 0)
    << "   E1^2*x1^(q-2)*e2(x1,x2,x3) in KK: " << ((E1^2*x1^(q-2)*e2p) % KK == 0) << endl;
  << "   without cross: " << (tgt % (ideal(g3,g5,E1^3)+monA+monB+box) == 0) << "  without g5: " << (tgt % (ideal(g3,E1^3)+cross+monA+monB+box) == 0)
    << "  without monA: " << (tgt % (ideal(g3,g5,E1^3)+cross+monB+box) == 0) << "  without monB: " << (tgt % (ideal(g3,g5,E1^3)+cross+monA+box) == 0) << endl;
  if q == 9 then << "   colength of eliminated K_2 (no E1^3): " << degree (ideal(g3,g5)+cross+monA+monB+box) << "  (N_2(9) = 855 expected)" << endl;
)
