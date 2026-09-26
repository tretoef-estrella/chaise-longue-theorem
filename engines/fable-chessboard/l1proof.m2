-- Explicit q-symbolic certificate for (L1), verified against the ORIGINAL conditions (I),(II) at q = 3, 9, 27, 81
for q in {3,9,27,81} do (
  R = ZZ/3[x1,x2,x3,x4]; xs = {x1,x2,x3,x4};
  boxq = ideal(x1^q,x2^q,x3^q,x4^q); boxq1 = ideal(x1^(q-1),x2^(q-1),x3^(q-1),x4^(q-1));
  e1 = x1+x2+x3+x4; e2 = x1*x2+x1*x3+x1*x4+x2*x3+x2*x4+x3*x4;
  e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
  T = (x1*x2)^(q-1)+(x3*x4)^(q-1);
  -- pairs (i,j | k,l) with sign s: +1 for the pairing 12|34, -1 for the cross pairs
  data = {{1,2,3,4,1},{3,4,1,2,1},{1,3,2,4,-1},{2,4,1,3,-1},{1,4,2,3,-1},{2,3,1,4,-1}};
  gamma1 = 0_R; U = 0_R;
  for t in data do (
    i = t#0; j = t#1; k = t#2; l = t#3; s = t#4;
    bij = xs#(i-1)+xs#(j-1); xk = xs#(k-1); xl = xs#(l-1);
    c = sum(1..(q-2), m -> (-1)^(m-1) * xk^(q-2-m) * xl^(m-1));   -- degree q-3
    gamma1 = gamma1 + s * bij^(q-1) * c;
    U = U + s * bij^(q-1) * xk * xl * c;
  );
  P0 = ((x1+x2)*(x3+x4))^(q-1); P1 = ((x1+x3)*(x2+x4))^(q-1); P2 = ((x1+x4)*(x2+x3))^(q-1);
  U = U + P0 - P1 - P2;
  dff = T - U;
  ok0 = (dff % e4 == 0);
  gamma0 = dff // e4;
  I1 = e1*(T - e4*gamma0) - (e1*e2-e3)*gamma1;
  I2 = e1*gamma1 + e3*gamma0;
  << "q=" << q << "  deg gamma0=" << (degree gamma0)#0 << " deg gamma1=" << (degree gamma1)#0
    << "  T-U divisible by e4: " << ok0
    << "  (I) holds mod box_q: " << (I1 % boxq == 0)
    << "  (II) holds mod box_{q-1}: " << (I2 % boxq1 == 0) << endl;
  -- also the identity (star) exactly: T + P0 - P1 - P2 - Q12 - Q34 + Q13 + Q24 + Q14 + Q23 == e4 * gamma0 (as polynomials)
  Q = (i,j,k,l) -> (xs#(i-1)+xs#(j-1))^(q-1) * (xs#(k-1)^(q-1) + xs#(l-1)^(q-1));
  star = T + P0 - P1 - P2 - Q(1,2,3,4) - Q(3,4,1,2) + Q(1,3,2,4) + Q(2,4,1,3) + Q(1,4,2,3) + Q(2,3,1,4);
  << "   (star): LHS == e4*gamma0 exactly: " << (star == e4*gamma0) << endl;
)
