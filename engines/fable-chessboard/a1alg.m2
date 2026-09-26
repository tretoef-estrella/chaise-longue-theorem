load "m10alg.m2";
for cell in {{9,5,2},{9,6,2},{9,6,3}} do (
  q := cell#0; n := cell#1; m := cell#2;
  (S, ys, c, d, J, B, GJ, GB, s) := setupAlg(q, n, m);
  << "=== (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " c=" << c << " d=" << d << endl << flush;
  -- (1) general A_r: all monomials
  t0 := cpuTime();
  cands := flatten apply(toList(0..(n-1)//2), r -> if d-2*r-1 < 0 then {} else apply(expsOf(n, d-2*r-1, q), e -> apply(toList(0..(n-1)//2), rr -> if rr == r then product apply(n, i -> (ys#i)^(e#i)) else 0_S)));
  (ok, M, sol) := solveAlg(S, ys, d, GJ, GB, s, cands);
  << "  general first-order A (" << #cands << " unknowns): solvable? " << ok << "  (" << cpuTime()-t0 << " s)" << endl << flush;
  -- (2) power-sum ansatz: A_r = sum_i g_i y_i^{n-2r-1}, g_i monomials of degree d-n
  t0 = cpuTime();
  cands2 := flatten apply(n, i -> apply(expsOf(n, d-n, q), e -> ( g := product apply(n, k -> (ys#k)^(e#k)); apply(toList(0..(n-1)//2), r -> if n-2*r-1 >= 0 then g * (ys#i)^(n-2*r-1) else 0_S))));
  (ok2, M2, sol2) := solveAlg(S, ys, d, GJ, GB, s, cands2);
  << "  power-sum descent ansatz (" << #cands2 << " unknowns): solvable? " << ok2 << "  (" << cpuTime()-t0 << " s)" << endl << flush;
);
<< "FIN-OK" << endl;
