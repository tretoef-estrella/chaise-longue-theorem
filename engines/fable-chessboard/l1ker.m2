-- Kernel of Mat = [[e1, -g3],[e3, -g5]] on (N2, N0) over A = R/box_q ; compare with families (a),(b); test T
for q in {3,9} do (
  R = ZZ/3[x1,x2,x3,x4]; box = ideal(x1^q,x2^q,x3^q,x4^q); A = R/box;
  e1 = x1+x2+x3+x4; e2 = x1*x2+x1*x3+x1*x4+x2*x3+x2*x4+x3*x4;
  e3 = x1*x2*x3+x1*x2*x4+x1*x3*x4+x2*x3*x4; e4 = x1*x2*x3*x4;
  g3 = e1*e2-e3; g5 = e1*e4; Pi = (x1+x2)*(x1+x3)*(x1+x4)*(x2+x3)*(x2+x4)*(x3+x4);
  T = (x1*x2)^(q-1)+(x3*x4)^(q-1);
  use A;
  -- M acts on (N2, N0) with deg N2 = 2q-2, deg N0 = 2q-4 (the relevant degree), but ker computed in all degrees
  K = ker map(A^2, A^2, matrix{{sub(e1,A), -sub(g3,A)},{sub(e3,A), -sub(g5,A)}});
  G = mingens K;
  << "q=" << q << " kernel mingens: " << numcols G << "  degrees(N2-row): " << tally apply(numcols G, i -> (degree G_(0,i), degree G_(1,i))) << endl;
  -- projection to N2 as an ideal of A
  P2 = ideal apply(numcols G, i -> G_(0,i));
  ann13 = ann ideal(sub(e1,A), sub(e3,A));
  prs = {{1,2,3,4},{3,4,1,2},{1,3,2,4},{2,4,1,3},{1,4,2,3},{2,3,1,4}};
  xs = {x1,x2,x3,x4};
  fam = ideal apply(prs, p -> (xs#(p#0-1)+xs#(p#1-1))^(q-1)*xs#(p#2-1)*xs#(p#3-1));
  fam = sub(fam,A);
  Kfam = fam + ann13;
  << "  pi2(Ker) == fam + ann(e1,e3)? " << (P2 == Kfam) << "   fam+ann subset pi2(Ker)? " << isSubset(Kfam, P2) << endl;
  << "  T in pi2(Ker) + (e4)? " << (sub(T,A) % (P2 + ideal sub(e4,A)) == 0) << endl;
  << "  T in fam + ann(e1,e3) + (e4)? " << (sub(T,A) % (Kfam + ideal sub(e4,A)) == 0) << endl;
  << "  T in ann(e1,e3) + (e4)? " << (sub(T,A) % (ann13 + ideal sub(e4,A)) == 0) << "   T in fam+(e4)? " << (sub(T,A) % (fam + ideal sub(e4,A)) == 0) << endl;
  -- degree-(2q-2) parts: dims
  << "  hilbert (2q-2): pi2(Ker) " << hilbertFunction(2*q-2, P2) << "  fam+ann " << hilbertFunction(2*q-2, Kfam) << "  ann13 " << hilbertFunction(2*q-2, ann13) << "  fam " << hilbertFunction(2*q-2, fam) << endl;
)
