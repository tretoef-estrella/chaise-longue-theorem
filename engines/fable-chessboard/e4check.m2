-- (E3),(E5) via the trick: z*f^h in I5 at q=9,27; is the cubic family needed? ; remaining (E4) sub-claim x1^(q-2)(x2-x3)^2 in K'_2 at q = 9,27,81
T = ZZ/3[x0,x2,x3,z];
e1p = x0+x2+x3+z; e2p = x0*x2+x0*x3+x0*z+x2*x3+x2*z+x3*z;
I7 = ideal(x2*x3*z*(x2+x3+z), x0*x3*z*(x0+x3+z), x0*x2*z*(x0+x2+z));
Inocubic = ideal(e1p^2, z^3, z*e2p, x0^3*z, x2^3*z, x3^3*z) + I7;
<< "z^2 x0^2 in Ieasy-without-cubics + I7: " << ((z^2*x0^2) % Inocubic == 0) << endl;
for q in {9,27,81} do (
  R = ZZ/3[x0,x1,x2,x3]; xs = {x0,x1,x2,x3}; box = ideal apply(xs, x -> x^q);
  e = j -> sum apply(subsets(xs, j), s -> product s);
  Mp = ideal flatten for a from 0 to 3 list for b from 0 to 3 list (if a != b then (product select(xs, x -> x != xs#a and x != xs#b)) * (xs#a)^(q-1) else 0_R);
  Kp2 = ideal(e 1, e 3, e 4) + Mp + box;
  eps2 = e 2;
  << "q=" << q << "  x1^(q-2)*eps2 in K'_2: " << ((x1^(q-2)*eps2) % Kp2 == 0)
    << "  x1^(q-2)*x3^3 in K'_2: " << ((x1^(q-2)*x3^3) % Kp2 == 0)
    << "  x1^(q-2)*(x2-x3)^2 in K'_2: " << ((x1^(q-2)*(x2-x3)^2) % Kp2 == 0)
    << "  x1^(q-2)*(x2^2+x3^2 - x0*(x1+x2+x3)) in K'_2: " << ((x1^(q-2)*(x2^2+x3^2-x0*(x1+x2+x3))) % Kp2 == 0) << endl;
  if q <= 27 then (
    S = ZZ/3[y0,y1,y2,y3,w]; vs = {y0,y1,y2,y3,w}; boxS = ideal apply(vs, v -> v^q);
    eS = j -> sum apply(subsets(vs, j), s -> product s);
    I5 = ideal(eS 1, eS 3, eS 5) + boxS;
    eps2S = sum apply(subsets({y0,y1,y2,y3}, 2), s -> product s);
    -- f_E3 = y1^(q-2) eps2 - y1^3 - y1 eps2 + y1 (degree q); f^h = w^q f(y/w); z f^h:
    fE3h = y1^(q-2)*eps2S - w^(q-3)*y1^3 - w^(q-2)*y1*eps2S + w^(q-1)*y1;
    << "   z*fE3^h in I5: " << ((w*fE3h) % I5 == 0) << "   => (E3) piece w*y1^(q-2)*eps2 in I5+(w^3): " << ((w*y1^(q-2)*eps2S) % (I5 + ideal(w^3)) == 0) << endl;
    Ssum = sum(0..(q-4), j -> y1^j * w^(q-4-j));
    fE5h = y3^3*y1^(q-2) - w^(q-1)*y1*y3 - w^(q-3)*y1*y3*(y3+w)*(y1+y3) - y1*y3*(y1+y3)*Ssum;
    << "   z*fE5^h in I5: " << ((w*fE5h) % I5 == 0) << "   => (E5): w*y1^(q-2)*y3^3 in I5+(w^3): " << ((w*y1^(q-2)*y3^3) % (I5 + ideal(w^3)) == 0) << endl;
  );
)
