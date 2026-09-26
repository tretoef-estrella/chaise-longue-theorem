-- q-free part of the colon: symmetric generators, q-free membership of the target, gates at q=81, lifts of x1^(q-2)*g
R = ZZ/3[x0,x1,x2,x3]; xs = {x0,x1,x2,x3};
E1 = sum xs; E2 = sum flatten for i from 0 to 3 list for j from i+1 to 3 list xs#i*xs#j;
E3 = sum flatten flatten for i from 0 to 3 list for j from i+1 to 3 list for k from j+1 to 3 list xs#i*xs#j*xs#k;
E4 = x0*x1*x2*x3; g3 = E1*E2-E3; g5 = E1*E4;
tau = x0+x2+x3; p2 = x0^2+x2^2+x3^2;
-- candidate symmetric generators of the q-free colon part
cand = {x1^2, E3, E1*p2, tau^3,
        x1*(x0+x2)*x0*x2, x1*(x0+x3)*x0*x3, x1*(x2+x3)*x2*x3,
        E1*x0^3, E1*x2^3, E1*x3^3,
        x0^2*(x2^2+x3^2-x0^2), x2^2*(x0^2+x3^2-x2^2), x3^2*(x0^2+x2^2-x3^2),
        (x2+x3)^2*(x1*(x2+x3)+x2*x3), (x0+x3)^2*(x1*(x0+x3)+x0*x3), (x0+x2)^2*(x1*(x0+x2)+x0*x2)};
Jlow = ideal cand;
<< "q-free: E1^2*x0^2 in Jlow? " << ((E1^2*x0^2) % Jlow == 0) << "   E1*Pi'*x1^(q-2)-form: E1*(x1+x2)*(x1+x3)*(x2+x3) in Jlow? " << ((E1*(x1+x2)*(x1+x3)*(x2+x3)) % Jlow == 0) << endl;
<< "mingens Jlow degrees: " << tally apply(numcols mingens Jlow, i -> (degree (mingens Jlow)_(0,i))#0) << endl;
for q in {9,27,81} do (
  box = ideal apply(xs, x -> x^q);
  cross = ideal flatten flatten for a from 0 to 3 list for i from 0 to 3 list for i2 from i+1 to 3 list (if i != a and i2 != a then (xs#i+xs#i2)*xs#i*xs#i2*xs#a^(q-1) else 0_R);
  K0 = ideal(g3, g5, E1^3) + cross + box;
  rr = apply(cand, g -> ((x1^(q-2)*g) % K0 == 0));
  << "q=" << q << " x1^(q-2)*g in K0 for each candidate: " << rr << endl;
  if q <= 27 then (
    J = K0 : x1^(q-2);
    << "   Jlow == (low part of colon)? Jlow subset J: " << isSubset(Jlow, J) << "   J subset Jlow + box: " << isSubset(J, Jlow + box) << endl;
  );
);
-- lifts at q = 9 for the non-obvious generators: E3, E1*p2, E1*x0^3, x0^2*(x2^2+x3^2-x0^2), (x2+x3)^2*(x1*(x2+x3)+x2*x3)
q = 9; box = ideal apply(xs, x -> x^q);
crossL = flatten flatten for a from 0 to 3 list for i from 0 to 3 list for i2 from i+1 to 3 list (if i != a and i2 != a then (xs#i+xs#i2)*xs#i*xs#i2*xs#a^(q-1) else 0_R);
crossL = select(crossL, f -> f != 0);
gensK = matrix{join({g3, g5, E1^3}, crossL, apply(xs, x -> x^q))};
nms = join({"g3","g5","E1^3"}, apply(crossL, f -> toString f), apply(xs, x -> toString(x^q)));
for g in {E3, E1*p2, E1*x0^3, x0^2*(x2^2+x3^2-x0^2), (x2+x3)^2*(x1*(x2+x3)+x2*x3)} do (
  L = (x1^(q-2)*g) // gensK;
  << "---- lift of x1^(q-2) * (" << g << ") at q=9:" << endl;
  for i from 0 to numrows L - 1 do if L_(i,0) != 0 then << "   [" << nms#i << "] * (" << L_(i,0) << ")" << endl;
);
