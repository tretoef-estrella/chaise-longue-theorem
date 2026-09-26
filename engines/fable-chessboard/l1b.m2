-- q=9 only. Unknowns gamma0 (deg 2q-6), gamma1 (deg 2q-4) in F_3[b1,b2,r1,r2], swap-symmetric (b1<->b2, r1<->r2),
-- with beta-degree caps cap0 on gamma0 and cap1 on gamma1. Solve (I),(II) mod box by linear algebra over F_3.
q = 9;
R = ZZ/3[a,ap,b,bp]; box = ideal(a^q, ap^q, b^q, bp^q); B = R/box;
e1 = a+ap+b+bp; e2 = a*ap+a*b+a*bp+ap*b+ap*bp+b*bp; e3 = a*ap*b+a*ap*bp+a*b*bp+ap*b*bp; e4 = a*ap*b*bp;
r1 = a*ap; r2 = b*bp; b1 = a+ap; b2 = b+bp; T = r1^(q-1) + r2^(q-1);
mon = (i,j,k,l) -> b1^i*b2^j*r1^k*r2^l;
-- swap-symmetric basis: orbit sums of (i,j,k,l) and (j,i,l,k), with i+j <= cap, i+j+2k+2l = d
symbasis = (d, cap) -> ( L := {};
  for i from 0 to cap do for j from 0 to cap-i do if (d-i-j) >= 0 and (d-i-j) % 2 == 0 then (
     s := (d-i-j)//2; for k from 0 to s do ( l := s-k;
        if (i,j,k,l) <= (j,i,l,k) then L = append(L, {(i,j,k,l),(j,i,l,k)})));
  L);
elt = orb -> ( if orb#0 == orb#1 then mon toSequence orb#0 else mon(toSequence orb#0) + mon(toSequence orb#1));
m1 = basis(2*q-1, B); m2 = basis(2*q+1, B);
vec = p -> ( (M1,C1) := coefficients(sub(p#0,B), Monomials=>m1); (M2,C2) := coefficients(sub(p#1,B), Monomials=>m2); sub(C1 || C2, ZZ/3) );
tv = vec (e1*T, e3*T);
trysolve = (cap0, cap1) -> (
  L0 := symbasis(2*q-6, cap0); L1 := symbasis(2*q-4, cap1);
  cols := apply(L0, o -> vec(e1*e4*elt o, e3*e4*elt o)) | apply(L1, o -> vec((e1*e2-e3)*elt o, e1*e4*elt o));
  A := fold((x,y) -> x | y, cols);
  sol := tv // A; ok := (A*sol == tv);
  << "cap0=" << cap0 << " cap1=" << cap1 << " unknowns " << #L0 << "+" << #L1 << " solvable? " << toString ok << endl;
  if ok then ( W := ZZ/3[B1,B2,R1,R2, Degrees=>{1,1,2,2}];
     monW := (i,j,k,l) -> B1^i*B2^j*R1^k*R2^l;
     eltW := orb -> ( if orb#0 == orb#1 then monW toSequence orb#0 else monW(toSequence orb#0) + monW(toSequence orb#1));
     n0 := #L0;
     g0 := sum(n0, i -> lift(sol_(i,0), ZZ/3) * eltW L0#i); g1 := sum(#L1, i -> lift(sol_(n0+i,0), ZZ/3) * eltW L1#i);
     << "  gamma0 (" << #terms g0 << " terms) = " << toString g0 << endl;
     << "  gamma1 (" << #terms g1 << " terms) = " << toString g1 << endl;);
  << flush; ok);
-- find minimal cap1 with cap0 = q-3
c1 = 0; while not trysolve(q-3, c1) do c1 = c1 + 2;
-- also try cap0 = q-3 with cap1 = q-1 and q+1 for comparison of sparsity
trysolve(q-3, q-1);
<< "FIN-OK" << endl; exit 0
