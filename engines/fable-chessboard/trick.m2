-- corrected homogenization checks: z*f^h in I5 for f_E3, f_E4, f_E5 ; and the q-free certificate of z^2 x0^2
for q in {9,27} do (
  S = ZZ/3[y0,y1,y2,y3,w]; vs = {y0,y1,y2,y3,w}; boxS = ideal apply(vs, v -> v^q);
  eS = j -> sum apply(subsets(vs, j), s -> product s);
  I5 = ideal(eS 1, eS 3, eS 5) + boxS;
  eps2 = sum apply(subsets({y0,y1,y2,y3}, 2), s -> product s); eps1 = y0+y1+y2+y3;
  -- E3: f = y1^(q-2) eps2 + y1^(q-2) eps1 - (y1^3 + y1 eps2 - y1 - y1^(q-2)), degree q; f^h:
  fE3h = y1^(q-2)*eps2 + w*y1^(q-2)*eps1 - w^(q-3)*y1^3 - w^(q-3)*y1*eps2 + w^(q-1)*y1 + w^2*y1^(q-2);
  << "q=" << q << "  w*fE3^h in I5: " << ((w*fE3h) % I5 == 0);
  -- E5: f = y3^3 y1^(q-2) - y1y3 - y1y3(y3+1)(y1+y3) - y1y3(y1+y3) sum_{j<=q-4} y1^j, degree q+1
  Ssum = sum(0..(q-4), j -> y1^j * w^(q-2-j));
  fE5h = y3^3*y1^(q-2) - w^(q-1)*y1*y3 - w^(q-3)*y1*y3*(y3+w)*(y1+y3) - y1*y3*(y1+y3)*Ssum;
  << "   w*fE5^h in I5: " << ((w*fE5h) % I5 == 0);
  -- E4: t = y1^(q-2)(y2^2+y3^2-y0(y1+y2+y3)), s = -y1^(q-2) y0, f = t + s - (y1^(q-2) + y1 + y1^3 + y1 eps2), degree q
  sig = y1+y2+y3;
  fE4h = y1^(q-2)*(y2^2+y3^2-y0*sig) - w*y1^(q-2)*y0 - w^2*y1^(q-2) - w^(q-1)*y1 - w^(q-3)*y1^3 - w^(q-3)*y1*eps2;
  << "   w*fE4^h in I5: " << ((w*fE4h) % I5 == 0) << endl;
  -- the cubic assembly: P - G0 == w*t + w^2*s exactly?
  cubic = y0*y2^2 + y2^3 - y0*y2*y3 - y2^2*y3 + y0*y3^2 - y2*y3^2 + y3^3 - y2^2*w - y2*y3*w - y3^2*w - y0*w^2;
  App = (y2-y3)^2 - y1*(y2+y3); b23 = y2+y3;
  G0 = y1^(q-2)*(eS 3) + y1^(q-2)*App*(eS 1) + y1^q*b23;
  << "   P - G0 == w*t + w^2*s: " << (y1^(q-2)*cubic - G0 == w*y1^(q-2)*(y2^2+y3^2-y0*sig) - w^2*y1^(q-2)*y0) << endl;
);
-- q-free certificate
T = ZZ/3[x0,x2,x3,z];
e1p = x0+x2+x3+z; e2p = x0*x2+x0*x3+x0*z+x2*x3+x2*z+x3*z;
cub = (a,b,c) -> a*b^2 + b^3 - a*b*c - b^2*c + a*c^2 - b*c^2 + c^3 - b^2*z - b*c*z - c^2*z - a*z^2;
gensL = matrix{{e1p^2, z^3, z*e2p, cub(x0,x2,x3), cub(x2,x0,x3), cub(x3,x0,x2), x0^3*z, x2^3*z, x3^3*z, x2*x3*z*(x2+x3+z), x0*x3*z*(x0+x3+z), x0*x2*z*(x0+x2+z)}};
nm = {"e1'^2","z^3","z e2'","cubic_0","cubic_2","cubic_3","x0^3 z","x2^3 z","x3^3 z","[7]_23","[7]_03","[7]_02"};
L = (z^2*x0^2) // gensL;
<< "q-free certificate of z^2 x0^2:" << endl;
for i from 0 to numrows L - 1 do if L_(i,0) != 0 then << "   (" << nm#i << ") * (" << L_(i,0) << ")" << endl;
<< "check: " << (gensL * L - matrix{{z^2*x0^2}} == 0) << endl;
