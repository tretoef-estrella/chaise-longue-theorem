load "m10alg.m2";
-- readable ansatz: A_r = sum lambda * y_j^al y_l^be e_k(y) e_k2(y)  (<= 2 elementary factors)
runSym = (q, n, m, nfac) -> (
  (S, ys, c, d, J, B, GJ, GB, s) := setupAlg(q, n, m);
  a := ys#0; b := ys#1;
  << "=== (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " c=" << c << " d=" << d << " factors<=" << nfac << endl << flush;
  t0 := cpuTime();
  cands := {}; labs := {};
  ks := if nfac == 1 then apply(toList(0..n), k -> {k}) else flatten apply(toList(0..n), k -> apply(toList(k..n), k2 -> {k,k2}));
  for r from 0 to (n-1)//2 do for kk in ks do ( dg := d-2*r-1 - sum kk; if dg >= 0 then for al from 0 to min(dg,q-1) do ( be := dg - al; if be <= q-1 then (
      A := apply(toList(0..(n-1)//2), rr -> if rr == r then a^al * b^be * product apply(kk, k -> esym(ys,k)) else 0_S);
      cands = append(cands, A); labs = append(labs, (r, al, be, kk)))));
  (ok, M, sol) := solveAlg(S, ys, d, GJ, GB, s, cands);
  << "  " << #cands << " unknowns, solvable? " << ok << " (" << cpuTime()-t0 << " s)" << endl << flush;
  if ok then (
    cur := select(toList(0..#cands-1), i -> sol_(i,0) != 0);
    for i in reverse cur do ( tr := delete(i, cur); (ok2, M2, sol2) := solveAlg(S, ys, d, GJ, GB, s, cands_tr); if ok2 then cur = tr );
    (ok3, M3, sol3) := solveAlg(S, ys, d, GJ, GB, s, cands_cur);
    << "  greedy-minimal support " << #cur << endl;
    for ii from 0 to #cur-1 do ( L := labs#(cur#ii); << "    A_" << L#0 << " += " << sol3_(ii,0) << " * a^" << L#1 << " b^" << L#2 << " e" << toString L#3 << endl);
  );
  << flush;
);
runSym(9,5,2,1);
runSym(9,5,1,1);
runSym(9,4,1,1);
runSym(27,5,2,1);
<< "FIN-OK" << endl;
