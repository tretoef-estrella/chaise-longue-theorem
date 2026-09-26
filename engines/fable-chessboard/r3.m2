load "m11lib.m2";
-- R3: (NC_ell) for parent (1^ell)(n+1) -> child (1^(ell+1))(n), row ell+1.  FIRST-ORDER ansatz:
--   z^ell * sum_r A_r e_{2r+1}(y,z)  with (T) sum A_r e_{2r+1}(y) in J_ell,  (Sh) sum A_r e_{2r}(y) == X' mod B_ell
--   J_ell := box + (e_k(y): k >= n-ell+1) + F^(ell)(n) [VZ child family] + (phi_{j,z}: pure-y parent members) [+ N_0(n) if ell=1]
--   B_ell := (e_k(y): k odd or k >= n-ell) + box
clSolve = (cands, GJ, GB, s, ys) -> (
  tops := apply(cands, A -> (sum apply(#A, r -> A#r * clE(ys, 2*r+1))) % GJ);
  shs := apply(cands, A -> (sum apply(#A, r -> A#r * clE(ys, 2*r))) % GB);
  (mt, Ct) := coefficients matrix{tops | {0_(ring s)}};
  (ms, Cs) := coefficients matrix{shs | {s % GB}};
  Mf := sub(Ct || Cs, ZZ/3); k := numcols Mf;
  M := submatrix(Mf, toList(0..k-2)); v := submatrix(Mf, {k-1});
  sol := v // M; (M * sol == v, sol));
runR3 = (q, np1, ell, nfac) -> (
  n := np1 - 1; S := ZZ/3[y_1..y_n, MonomialOrder=>GRevLex]; ys := gens S;
  t0 := cpuTime();
  Jg := apply(ys, v -> v^q) | apply(select(toList(1..n), k -> k >= n-ell+1), k -> clE(ys,k));
  for j from 0 to n-1 do for l from 0 to n-1 do if j != l then Jg = append(Jg, clPhi(ys, q, ell, n-2, j, l));
  for j from 0 to n-1 do Jg = append(Jg, (ys#j)^(q-ell) * sum apply(toList(0..ell-1), i -> (ys#j)^i * clE(drop(ys,{j,j}), n-1-i)));
  if ell == 1 then Jg = Jg | clLayer(ys, 0, q);
  Bg := apply(ys, v -> v^q) | apply(select(toList(1..n), k -> odd k or k >= n-ell), k -> clE(ys,k));
  GJ := gb ideal Jg; GB := gb ideal Bg;
  s := clPhi(ys, q, ell+1, n-2, 0, 1);   -- X' = child family, j = y_1, l = y_2
  a := ys#0; b := ys#1;
  dd := q + n - ell - 3;   -- deg A_0
  ks := if nfac == 0 then {{}} else if nfac == 1 then apply(toList(0..n), k -> {k}) else flatten apply(toList(0..n), k -> apply(toList(k..n), k2 -> {k,k2}));
  cands := {}; labs := {};
  R := (n-1)//2;
  for r from 0 to R do for kk in ks do ( dg := dd - 2*r - sum kk; if dg >= 0 then for al from 0 to min(dg,q-1) do ( be := dg - al; if be <= q-1 then (
      A := apply(toList(0..R), rr -> if rr == r then a^al * b^be * product apply(kk, k -> clE(ys,k)) else 0_S);
      cands = append(cands, A); labs = append(labs, (r, al, be, kk)))));
  (ok, sol) := clSolve(cands, GJ, GB, s, ys);
  << "=== q=" << q << " parent (1^" << ell << ") n+1=" << np1 << " e-factors<=" << nfac << " : " << #cands << " unknowns, solvable? " << ok << " [" << cpuTime()-t0 << "s]" << endl << flush;
  if ok then (
    cur := select(toList(0..#cands-1), i -> sol_(i,0) != 0);
    for i in reverse cur do ( tr := delete(i, cur); (ok2, sol2) := clSolve(cands_tr, GJ, GB, s, ys); if ok2 then cur = tr );
    (ok3, sol3) := clSolve(cands_cur, GJ, GB, s, ys);
    << "  greedy-minimal support " << #cur << endl;
    for ii from 0 to #cur-1 do ( L := labs#(cur#ii); << "    A_" << L#0 << " += " << sol3_(ii,0) << " * a^" << L#1 << " b^" << L#2 << " e" << toString L#3 << endl);
  );
  << flush;
);
runR3(9,5,1,0); runR3(9,6,1,0);
runR3(9,5,2,0); runR3(9,6,2,0);
runR3(9,6,3,0);
runR3(9,5,2,1); runR3(9,6,2,1); runR3(9,6,3,1);
<< "FIN-OK" << endl;
