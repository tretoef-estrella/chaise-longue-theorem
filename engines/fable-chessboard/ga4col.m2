-- colon (K0 : x1^(q-2)) at q = 9, 27: low-degree generators; and a lift of the target
for q in {9,27} do (
  R = ZZ/3[x0,x1,x2,x3]; xs = {x0,x1,x2,x3};
  box = ideal apply(xs, x -> x^q);
  E1 = sum xs;
  E2 = sum flatten for i from 0 to 3 list for j from i+1 to 3 list xs#i*xs#j;
  E3 = sum flatten flatten for i from 0 to 3 list for j from i+1 to 3 list for k from j+1 to 3 list xs#i*xs#j*xs#k;
  E4 = x0*x1*x2*x3;
  g3 = E1*E2 - E3; g5 = E1*E4;
  crossL = flatten flatten for a from 0 to 3 list for i from 0 to 3 list for i2 from i+1 to 3 list (if i != a and i2 != a then (xs#i+xs#i2)*xs#i*xs#i2*xs#a^(q-1) else 0_R);
  cross = ideal crossL;
  K0 = ideal(g3, g5, E1^3) + cross + box;
  tgt = E1^2*x0^2*x1^(q-2);
  << "q=" << q << " tgt in K0: " << (tgt % K0 == 0) << endl;
  J = K0 : x1^(q-2);
  MJ = mingens J;
  << "  colon mingens degrees: " << tally apply(numcols MJ, i -> (degree MJ_(0,i))#0) << endl;
  low = select(numcols MJ, i -> (degree MJ_(0,i))#0 <= 6);
  << "  low-degree (<=6) generators of the colon:" << endl;
  for i in low do << "    " << MJ_(0,i) << endl;
  -- the x1-free reduction: colon mod x1^2 in degrees <= 4
  << "  tgt/x1^(q-2) = E1^2 x0^2 in colon: " << ((E1^2*x0^2) % J == 0) << endl;
)
