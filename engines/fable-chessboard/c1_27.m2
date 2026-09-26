-- Gate q=27 for the single-congruence form (C_1) with G-invariant unknowns, beta-degree caps (q-3, q-1).
-- Products built inside the quotient ring Bc = Ry/(x^{q-1}, yj^{q-1}) to keep them small. Then verify (I),(II) in Ry/box.
q = 27;
Ry = ZZ/3[x,y2,y3,y4];
x1 = x; x2 = y2-x; x3 = y3-x; x4 = y4-x;
r1 = x1*x2; r2 = x3*x4; b1 = x1+x2; b2 = x3+x4;
e1 = x1+x2+x3+x4; e2 = x1*x2+x1*x3+x1*x4+x2*x3+x2*x4+x3*x4; e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
T = r1^(q-1) + r2^(q-1);
s1 = x2+x3+x4; s3 = x2*x3*x4;
Ib = ideal(x^q, y2^(q-1), y3^(q-1), y4^(q-1)); Ic = ideal(x^(q-1), y2^(q-1), y3^(q-1), y4^(q-1)); box = ideal(x1^q, x2^q, x3^q, x4^q);
Bb = Ry/Ib; use Ry; Bc = Ry/Ic; use Ry; Bq = Ry/box; use Ry;
Tred = lift(sub(T, Bb), Ry); L1 = Tred // x;
<< "T mod b1 divisible by x^2? " << toString(Tred % x^2 == 0) << endl << flush;
b1B = sub(b1,Bc); b2B = sub(b2,Bc); r1B = sub(r1,Bc); r2B = sub(r2,Bc); s1B = sub(s1,Bc); s3B = sub(s3,Bc);
pw = (g, n) -> ( t := 1_Bc; for i from 1 to n do t = t*g; t );
Pb1 = apply(q, i -> pw(b1B,i)); Pb2 = apply(q, i -> pw(b2B,i)); Pr1 = apply(q, i -> pw(r1B,i)); Pr2 = apply(q, i -> pw(r2B,i));
monB = (i,j,k,l) -> Pb1#i * Pb2#j * Pr1#k * Pr2#l;
symbasis = (d, cap) -> ( L := {};
  for i from 0 to cap do for j from 0 to cap-i do if (d-i-j) >= 0 and (d-i-j) % 2 == 0 then (
     s := (d-i-j)//2; for k from 0 to s do ( l := s-k;
        if (i,j,k,l) <= (j,i,l,k) then L = append(L, {(i,j,k,l),(j,i,l,k)})));
  L);
eltB = orb -> ( if orb#0 == orb#1 then monB toSequence orb#0 else monB(toSequence orb#0) + monB(toSequence orb#1));
L0 = symbasis(2*q-6, q-3); L1s = symbasis(2*q-4, q-1);
<< "unknowns " << #L0 << "+" << #L1s << endl << flush;
mc = basis(2*q-3, Bc); << "rows " << numgens source mc << endl << flush;
vec = p -> ( (M,C) := coefficients(p, Monomials=>mc); sub(C,ZZ/3) );
cols = apply(L0, o -> vec(s3B*eltB o)) | apply(L1s, o -> vec(s1B*eltB o));
<< "columns built" << endl << flush;
A = fold((a,b)->a|b, cols); tv = vec sub(L1,Bc);
sol = tv // A; ok = (A*sol == tv);
<< "q=27 (C_1) G-invariant caps (q-3,q-1): solvable? " << toString ok << endl << flush;
if ok then ( n0 := #L0;
  mon := (i,j,k,l) -> b1^i*b2^j*r1^k*r2^l;
  elt := orb -> ( if orb#0 == orb#1 then mon toSequence orb#0 else mon(toSequence orb#0) + mon(toSequence orb#1));
  g0 := sum(n0, i -> lift(sol_(i,0),ZZ/3)*elt L0#i); g1 := sum(#L1s, i -> lift(sol_(n0+i,0),ZZ/3)*elt L1s#i);
  U := T - e4*g0;
  << "  (I) holds? " << toString(sub(e1*U - (e1*e2-e3)*g1, Bq) == 0) << endl;
  << "  (II) holds? " << toString(sub(e3*U - e1*e4*g1, Bq) == 0) << endl;);
<< "FIN-OK" << endl; exit 0
