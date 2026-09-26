-- 5-variable: x1-free part of (K2+(z^3)) : x1^(q-2), low degrees, q=9,27; status of extras w.r.t. I5+(z^3)
for q in {9,27} do (
  S = ZZ/3[x0,x1,x2,x3,z]; vs = {x0,x1,x2,x3,z}; zz = vs#4;
  box = ideal apply(vs, v -> v^q);
  e = j -> sum apply(subsets(vs, j), s -> product s);
  I5 = ideal(e 1, e 3, e 5) + box;
  M1 = ideal flatten for a from 0 to 4 list for b from 0 to 4 list (if a != b then (product select(vs, v -> v != vs#a and v != vs#b)) * (vs#a)^(q-1) else 0_S);
  M2 = ideal flatten for A in subsets(5,2) list for c from 0 to 4 list (if not member(c, A) then vs#c * product apply(A, a -> (vs#a)^(q-1)) else 0_S);
  K2 = I5 + M1 + M2;
  C = (K2 + ideal(zz^3)) : (vs#1)^(q-2);
  Cf = eliminate(vs#1, C);
  MC = mingens Cf;
  << "q=" << q << "  x1-free colon mingens degrees " << tally apply(numcols MC, i -> (degree MC_(0,i))#0) << endl;
  lowidx = select(numcols MC, i -> (degree MC_(0,i))#0 <= 6);
  for i in lowidx do << "    [" << i << "] " << MC_(0,i) << "   in (I5+(z^3)):x1^(q-2)? " << (((vs#1)^(q-2)*MC_(0,i)) % (I5 + ideal(zz^3)) == 0) << endl;
  << "  z^2*x0^2 in x1-free colon: " << ((zz^2*(vs#0)^2) % Cf == 0) << endl;
  Clow = ideal apply(lowidx, i -> MC_(0,i));
  << "  z^2*x0^2 in the LOW part alone (q-free): " << ((zz^2*(vs#0)^2) % Clow == 0) << endl;
  -- the sub-lemma (b) simplification: beta01 * x1^(q-2) * e2(x1,x2,x3) in I5 + (z^3) ?
  << "  (b'): (x0+x1)*x1^(q-2)*e2(x1,x2,x3) in I5+(z^3): " << (((vs#0+vs#1)*(vs#1)^(q-2)*(vs#1*vs#2+vs#1*vs#3+vs#2*vs#3)) % (I5 + ideal(zz^3)) == 0) << endl;
  << "  (b): x1^(q-2)*z*(x0^2+x2^2+x3^2) in I5+(z^3): " << (((vs#1)^(q-2)*zz*((vs#0)^2+(vs#2)^2+(vs#3)^2)) % (I5 + ideal(zz^3)) == 0) << endl;
)
