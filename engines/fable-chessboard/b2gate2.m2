load "m10unif.m2";
gateU2 = (q, n, mu, dl) -> (
  t0 := cpuTime();
  (S, ys, G, tm) := casilla(q, n, mu, toList(0..#mu-1), dl);
  ell := #mu; f := n - sum mu;
  K := Qmu(S, ys, mu) + ideal apply(ys, v -> v^q) + layerN(ys, mu#0 - 1, q) + famPhi(ys, q, ell, f + ell - 2);
  K = ideal mingens K;
  eq := (K == G);
  << "mu=" << toString mu << " n=" << n << " f=" << f << " |W|=" << degree G << " : K_unif == G (as ideals)? " << eq << (if not eq then " colength K = " | toString degree K else "") << "  [" << cpuTime()-t0 << " s]" << endl << flush;
);
profs = {{3,1},{4,1},{2,2},{3,2},{1,1,1},{2,1,1},{3,1,1},{2,2,1},{1,1,1,1},{2,1,1,1}};


