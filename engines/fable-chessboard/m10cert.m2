load "m10alg.m2";
-- closed-form certificate A_r = (-1)^c sum_{1<=i<=q-1, 1<=D-i<=q-1} (-a)^i b^(D-i), D = q+c-2-2r, r <= c/2
certA = (S, ys, q, c) -> ( a := ys#0; b := ys#1; n := #ys;
  apply(toList(0..(n-1)//2), r -> if 2*r > c then 0_S else ( D := q+c-2-2*r;
     (-1)^c * sum(select(toList(1..q-1), i -> D-i >= 1 and D-i <= q-1), i -> (-a)^i * b^(D-i)))));
checkCell = (q, n, m) -> (
  t0 := cpuTime();
  (S, ys, c, d, J, B, GJ, GB, s) := setupAlg(q, n, m);
  A := certA(S, ys, q, c);
  top := sum apply(#A, r -> A#r * esym(ys, 2*r+1));
  sh := sum apply(#A, r -> A#r * esym(ys, 2*r));
  okT := (top % GJ) == 0; okS := ((sh - s) % GB) == 0;
  << "cell (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " n=" << n << " c=" << c << " : (T) top in J? " << okT << " ; (Sh) shadow = s mod B? " << okS << "   [" << cpuTime()-t0 << " s]" << endl << flush;
  (okT, okS));
