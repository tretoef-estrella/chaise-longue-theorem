-- explicit lifts of T in F + (P0,P1,P2) + (e4) + box, q=3,9 ; membership tests at q=27
needsPackage "Elimination";
for q in {3,9,27} do (
  R = ZZ/3[x1,x2,x3,x4]; box = ideal(x1^q,x2^q,x3^q,x4^q);
  e1 = x1+x2+x3+x4; e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
  T = (x1*x2)^(q-1)+(x3*x4)^(q-1);
  bb = (i,j) -> R_(i-1)+R_(j-1);
  F12 = (bb(1,2))^(q-1)*x3*x4; F34 = (bb(3,4))^(q-1)*x1*x2; F13 = (bb(1,3))^(q-1)*x2*x4; F24 = (bb(2,4))^(q-1)*x1*x3; F14 = (bb(1,4))^(q-1)*x2*x3; F23 = (bb(2,3))^(q-1)*x1*x4;
  P0 = (bb(1,2)*bb(3,4))^(q-1); P1 = (bb(1,3)*bb(2,4))^(q-1); P2 = (bb(1,4)*bb(2,3))^(q-1);
  Jp = ideal(F12,F34,F13,F24,F14,F23,P0,P1,P2,e4) + box;
  << "q=" << q << "  T in F + (P0,P1,P2) + (e4) + box? " << (T % Jp == 0) << endl;
  << "   T in F + (e4) + box? " << (T % (ideal(F12,F34,F13,F24,F14,F23,e4)+box) == 0) << "   T in F+(P0)+(e4)+box? " << (T % (ideal(F12,F34,F13,F24,F14,F23,P0,e4)+box) == 0) << "   T in F+(P1,P2)+(e4)+box? " << (T % (ideal(F12,F34,F13,F24,F14,F23,P1,P2,e4)+box) == 0) << endl;
  << "   T in (F12,F34)+(P0,P1,P2)+(e4)+box? " << (T % (ideal(F12,F34,P0,P1,P2,e4)+box) == 0) << "   T in (F13,F24,F14,F23)+(P0,P1,P2)+(e4)+box? " << (T % (ideal(F13,F24,F14,F23,P0,P1,P2,e4)+box) == 0) << endl;
  if q <= 9 then (
    A = R/box; use A;
    gensJ = matrix{{sub(F12,A),sub(F34,A),sub(F13,A),sub(F24,A),sub(F14,A),sub(F23,A),sub(P0,A),sub(P1,A),sub(P2,A),sub(e4,A)}};
    L = sub(T,A) // gensJ;
    << "   lift coefficients (F12,F34,F13,F24,F14,F23,P0,P1,P2,e4):" << endl;
    for i from 0 to 9 do << "     [" << i << "] " << L_(i,0) << endl;
  );
)
