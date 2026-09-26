load "m10alg.m2";
-- e-h descent ansatz: A_r = g * h_{t-2r-1}(X), X subset of [n], |X| = p, g monomial, t = d - deg g
hsym = (L, k) -> if k < 0 then 0_(ring L#0) else if k == 0 then 1_(ring L#0) else sum apply(flatten apply(compositionsOf(#L, k), c -> {c}), c -> product apply(#L, i -> (L#i)^(c#i)));
compositionsOf = (p, k) -> if p == 1 then {{k}} else flatten apply(toList(0..k), a -> apply(compositionsOf(p-1, k-a), c -> prepend(a, c)));
for cell in {{9,5,2}} do (
  q := cell#0; n := cell#1; m := cell#2;
  (S, ys, c, d, J, B, GJ, GB, s) := setupAlg(q, n, m);
  << "=== (n+1,m)=(" << n+1 << "," << m << ") q=" << q << " c=" << c << " d=" << d << endl << flush;
  for Xs in { {{0,1}}, subsets(n,2), subsets(n,1) | subsets(n,2), subsets(n,3), subsets(n,1)|subsets(n,2)|subsets(n,3) } do (
    t0 := cpuTime();
    cands := flatten flatten apply(Xs, X -> apply(toList(0..d-1), dg -> apply(expsOf(n, dg, q), e -> ( g := product apply(n, k -> (ys#k)^(e#k)); tt := d - dg;
       apply(toList(0..(n-1)//2), r -> g * hsym(apply(X, i -> ys#i), tt-2*r-1))))));
    cands = select(cands, A -> any(A, a -> a != 0));
    (ok, M, sol) := solveAlg(S, ys, d, GJ, GB, s, cands);
    << "  X-family " << toString take(Xs,3) << "... (" << #Xs << " sets, " << #cands << " unknowns): solvable? " << ok << "  (" << cpuTime()-t0 << " s)" << endl << flush;
  );
);
<< "FIN-OK" << endl;
