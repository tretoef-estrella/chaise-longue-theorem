-- MISSION 10, A0/A1: certificate of (G1): z^2 s in E := I^(n+1) + z*Ntilde_{m-1}(n) + (z^3)
-- usage: set qq, nn (=n+1), mm before loading; prints the reduced certificate by generator type
esym = (L,j) -> if j > #L or j < 0 then 0_(ring L#0) else if j == 0 then 1_(ring L#0) else sum apply(subsets(L,j), s -> product s);
layerGens = (V, w, q) -> ( nv := #V; out := {};
  for a from 0 to nv do for b from max(1, 0) to nv - a do ( c := nv - a - b; if c >= 0 and b - a <= w and b >= 1 then
    for A in subsets(nv, a) do for Bs in subsets(select(toList(0..nv-1), i -> not member(i,A)), b) do (
      C := select(toList(0..nv-1), i -> not member(i,A) and not member(i,Bs));
      out = append(out, ((product apply(C, i -> V#i)) * (product apply(A, i -> (V#i)^(q-1))), {a,b,c}, A, C))));
  out);
runCell = (q, nn, m) -> (
  n := nn - 1; c := n - m - 1;
  S := ZZ/3[y_1..y_n, z, MonomialOrder => GRevLex]; ys := take(gens S, n); zz := z;
  allv := gens S;
  Godd := apply(select(toList(1..nn), j -> odd j), j -> esym(allv, j));
  Gbox := apply(allv, v -> v^q);
  lay := layerGens(ys, m-1, q);
  -- keep only minimal layer monomials
  laym := flatten entries mingens ideal apply(lay, t -> t#0);
  layI := select(lay, t -> member(t#0, laym));
  Gen := if even nn and m >= 1 then {zz * esym(ys, n)} else {};
  G := Godd | Gbox | apply(layI, t -> zz * t#0) | Gen | {zz^3};
  types := apply(Godd, g -> "e_odd") | apply(Gbox, g -> "box") | apply(layI, t -> "z*lay" | toString(t#1)) | apply(Gen, g -> "z*e_n") | {"z^3"};
  M := matrix{G};
  s := (ys#0)^(q-2) * esym(drop(ys, {1,1}), c);
  f := zz^2 * s;
  t0 := cpuTime();
  cf := (matrix{{f}}) // M;
  << "cell (n+1,m)=(" << nn << "," << m << ") q=" << q << " c=" << c << " : lift ok? " << (M * cf == matrix{{f}}) << "  (" << cpuTime()-t0 << " s)" << endl << flush;
  cf = cf % ideal(zz^3) ; -- coefficients mod z^3 suffice for z^0..z^2 comparison? (only approximate; keep raw below)
  cf = (matrix{{f}}) // M;
  t0 = cpuTime();
  Z := syz M;
  << "  syz computed: " << numcols Z << " columns (" << cpuTime()-t0 << " s)" << endl << flush;
  t0 = cpuTime();
  cr := cf % image Z;
  << "  reduced mod syz; still a certificate? " << (M * cr == matrix{{f}}) << "  (" << cpuTime()-t0 << " s)" << endl << flush;
  nz := select(toList(0..numrows cr - 1), i -> cr_(i,0) != 0);
  << "  nonzero coefficients: " << #nz << " of " << numrows cr << " ; total terms " << sum apply(nz, i -> #terms cr_(i,0)) << endl;
  << "  by type: " << tally apply(nz, i -> types#i) << endl;
  for i in nz do (
    co := cr_(i,0);
    zparts := apply(3, k -> sum select(terms co, t -> (degree(zz, t)) == k));
    << "  [" << types#i << "] gen=" << (if types#i == "e_odd" then "e_" | toString(first degree G#i) else toString G#i) << endl;
    for k from 0 to 2 do if zparts#k != 0 then << "      z^" << k << ": " << toString(zparts#k) << endl;
    hi := sum select(terms co, t -> (degree(zz,t)) >= 3); if hi != 0 then << "      z^>=3: " << #terms hi << " terms" << endl;
  );
  << flush;
  (S, M, cr, types)
);
