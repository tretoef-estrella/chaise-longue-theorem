load "m10cas.m2";
-- (1,1,1) at n = 7, q = 9: truncated GB, top forms, colength certificate (target 20370)
(S, ys, I) = trueCas(9, 7, {1,1,1}, {0,1,2});
for dl in {14, 15, 16, 17, 18, 20, 22, 24} do (
  t0 := cpuTime(); G := gb(I, DegreeLimit => dl); J := topForms(S, G);
  cl := degree J;
  << "DegreeLimit " << dl << " : colength of top forms " << cl << " (target 20370) [" << cpuTime()-t0 << " s]" << endl << flush;
  if cl == 20370 then (
    mg := flatten entries mingens J;
    << "  mingens by degree " << toString sort pairs tally apply(mg, g -> first degree g) << endl;
    hi := select(mg, g -> first degree g >= 10);
    << "  degree >= 10 mingens: " << #hi << endl;
    for g in take(hi, 12) do << "    [" << first degree g << ", " << #terms g << " terms] " << toString g << endl;
    << "  #terms distribution (deg>=10): " << toString sort pairs tally apply(hi, g -> #terms g) << endl;
    break;
  );
);
<< "FIN-OK" << endl;
