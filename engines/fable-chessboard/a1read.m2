load "m10alg.m2";
hsym = (L, k) -> if k < 0 then 0_(ring L#0) else if k == 0 then 1_(ring L#0) else sum apply(compositionsOf(#L, k), c -> product apply(#L, i -> (L#i)^(c#i)));
compositionsOf = (p, k) -> if p == 1 then {{k}} else flatten apply(toList(0..k), a -> apply(compositionsOf(p-1, k-a), c -> prepend(a, c)));
okey = e -> (e#0, e#1, sort drop(e, 2));
-- unknowns: g = y_j^a y_l^b * (S_P-orbit sum of a monomial on P);  A_r = g*h_{t-2r-1}(y_j,y_l), t = d - deg g
runRead = (q, n, m) -> (
  (S, ys, c, d, J, B, GJ, GB, s) := setupAlg(q, n, m);
  << "=== (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " c=" << c << " d=" << d << endl << flush;
  t0 := cpuTime();
  gl := {}; glab := {};
  for dg from 0 to d-1 do (
    E := expsOf(n, dg, q); ks := unique apply(E, okey);
    for k in ks do ( g := sum apply(select(E, e -> okey e == k), e -> product apply(n, i -> (ys#i)^(e#i)));
      gl = append(gl, g); glab = append(glab, k)));
  cands := apply(gl, g -> ( tt := d - first degree g; apply(toList(0..(n-1)//2), r -> g * hsym({ys#0, ys#1}, tt-2*r-1))));
  (ok, M, sol) := solveAlg(S, ys, d, GJ, GB, s, cands);
  << "  S_P-invariant g, X={j,l}: " << #cands << " unknowns, solvable? " << ok << " (" << cpuTime()-t0 << " s)" << endl << flush;
  if not ok then return;
  -- sparsify: greedy removal of unknowns
  keep := select(toList(0..#cands-1), i -> sol_(i,0) != 0);
  << "  raw support " << #keep << endl;
  kerM := gens ker M;
  cur := keep;
  for i in reverse keep do ( tr := delete(i, cur); (ok2, M2, sol2) := solveAlg(S, ys, d, GJ, GB, s, cands_tr); if ok2 then cur = tr );
  (ok3, M3, sol3) := solveAlg(S, ys, d, GJ, GB, s, cands_cur);
  << "  minimal support " << #cur << " : " << endl;
  for ii from 0 to #cur-1 do ( i := cur#ii; << "    coef " << sol3_(ii,0) << " * g = y_j^" << (glab#i)#0 << " y_l^" << (glab#i)#1 << " * orb_P" << toString((glab#i)#2) << "   (t = " << d - first degree gl#i << ")" << endl);
  << flush;
);
runRead(9,5,2);
runRead(27,5,2);
<< "FIN-OK" << endl;
