-- Single-congruence form of (L1) at q=9 (G-invariant unknowns):
-- (C_1'): sigma3^(1)*g0 + sigma1^(1)*g1 == L1 mod c1 = (x^{q-1}, y2^{q-1}, y3^{q-1}, y4^{q-1}),  x=x1, yj = x1+xj,
-- L1 = (r2^{q-1} reduced mod (x^q, yj^{q-1}))/x.  Then check (I),(II) in the original ring.
q = 9;
Ry = ZZ/3[x,y2,y3,y4]; 
x1 = x; x2 = y2-x; x3 = y3-x; x4 = y4-x;
r1 = x1*x2; r2 = x3*x4; b1 = x1+x2; b2 = x3+x4;
e1 = x1+x2+x3+x4; e2 = x1*x2+x1*x3+x1*x4+x2*x3+x2*x4+x3*x4; e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
T = r1^(q-1) + r2^(q-1);
s1 = x2+x3+x4; s3 = x2*x3*x4;
Ib = ideal(x^q, y2^(q-1), y3^(q-1), y4^(q-1)); Ic = ideal(x^(q-1), y2^(q-1), y3^(q-1), y4^(q-1)); box = ideal(x1^q, x2^q, x3^q, x4^q);
Bb = Ry/Ib; use Ry; Bc = Ry/Ic; use Ry; Bq = Ry/box; use Ry;
Tred = lift(sub(T, Bb), Ry);   -- T mod b_1
<< "T mod b1 divisible by x^2? " << toString(Tred % x^2 == 0) << endl;
L1 = Tred // x;
mon = (i,j,k,l) -> b1^i*b2^j*r1^k*r2^l;
symbasis = (d, cap) -> ( L := {};
  for i from 0 to cap do for j from 0 to cap-i do if (d-i-j) >= 0 and (d-i-j) % 2 == 0 then (
     s := (d-i-j)//2; for k from 0 to s do ( l := s-k;
        if (i,j,k,l) <= (j,i,l,k) then L = append(L, {(i,j,k,l),(j,i,l,k)})));
  L);
elt = orb -> ( if orb#0 == orb#1 then mon toSequence orb#0 else mon(toSequence orb#0) + mon(toSequence orb#1));
L0 = symbasis(2*q-6, 2*q-6); L1s = symbasis(2*q-4, 2*q-4);
mc = basis(2*q-3, Bc);
vec = p -> ( (M,C) := coefficients(sub(p,Bc), Monomials=>mc); sub(C,ZZ/3) );
cols = apply(L0, o -> vec(s3*elt o)) | apply(L1s, o -> vec(s1*elt o));
A = fold((a,b)->a|b, cols); tv = vec L1;
sol = tv // A; ok = (A*sol == tv);
<< "q=9 (C_1') G-invariant: unknowns " << #L0 << "+" << #L1s << " rows " << numgens target A << " solvable? " << toString ok << " kernel dim " << (#L0+#L1s - rank A) << endl;
if ok then ( n0 := #L0;
  g0 := sum(n0, i -> lift(sol_(i,0),ZZ/3)*elt L0#i); g1 := sum(#L1s, i -> lift(sol_(n0+i,0),ZZ/3)*elt L1s#i);
  U := T - e4*g0;
  << "  (I) holds? " << toString(sub(e1*U - (e1*e2-e3)*g1, Bq) == 0) << endl;
  << "  (II) holds? " << toString(sub(e3*U - e1*e4*g1, Bq) == 0) << endl;
  -- and the four (C_i) directly
  X := {x1,x2,x3,x4};
  for i from 0 to 3 do ( PP := product(select(X, y -> y =!= X#i), y -> X#i + y);
     << "  (C_" << i+1 << ") holds? " << toString(sub(PP*(U - g1*(X#i)*(e1-X#i)), Bq) == 0) << endl;););
<< "FIN-OK" << endl; exit 0
