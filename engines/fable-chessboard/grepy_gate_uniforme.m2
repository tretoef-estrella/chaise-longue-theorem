-- WARNING (auditor, 2026-09-23, MISSION 12): the uniform casilla is FALSE at (1,1) n=7,8 and (2,2) n=7 (q=9).
-- This engine truncates the INHOMOGENEOUS fibre ideal with DegreeLimit, which cannot certify there. To certify, use grepy_casilla_verdadera.py.
-- regla259 (Grepy el Lector): gate the uniform casilla of INFORME_10 AS AN IDEAL, own code, different route.
-- Family written in the FERMION form: phi_jl = y_j^(q-l) * sum_k y_j^(2k) e_{f+l-2-2k}(y \ y_l)  (== Fable's boson sum mod box).
-- G = true casilla gr I(W_mu(n)) (top forms of a GRevLex GB of the fibre ideal), optional DegreeLimit + colength certificate.
clEl = (clv, clr) -> (if clr < 0 then return 0; if clr == 0 then return 1; if clr > #clv then return 0; sum(subsets(clv, clr), clt -> product clt));
clTop = clg -> part((degree clg)#0, clg);
clGate = (clq, clmu, cln, clwant, cldl) -> clGateX(clq, clmu, cln, clwant, cldl, 0);
clGateX = (clq, clmu, cln, clwant, cldl, clpert) -> (
  clKK := GF(clq, Variable=>cla);
  clS := clKK[clx_1..clx_cln, MonomialOrder=>GRevLex]; use clS;
  clV := gens clS; clell := #clmu; clM := sum clmu; clf := cln - clM;
  clAnch := flatten for cli from 0 to clell-1 list toList(clmu#cli : (cla^cli));
  clRel := for clj from 1 to cln+clM list (if even clj then continue; sum(0..clM, clr -> clEl(clAnch, clr) * clEl(clV, clj-clr)));
  clI := ideal clRel + ideal apply(clV, clv -> clv^clq - clv);
  clt0 := cpuTime();
  clGB := if cldl > 0 then flatten entries gens gb(clI, DegreeLimit=>cldl) else flatten entries gens gb clI;
  clG := ideal apply(clGB, clTop);
  clcolG := degree(clS/clG);
  -- Q_mu(n): mission 3.3.8
  cllam := clmu | toList(clf:1);
  cllc := apply(toList(1..cln), cli -> #select(cllam, clx -> clx >= cli));
  cldk := clk -> sum take(reverse cllc, clk);
  clQ := apply(select(toList(1..cln), clj -> odd clj or clj >= cln - clM + 1), clj -> clEl(clV, clj));
  for clk from 1 to cln-1 do for clSs in subsets(cln, clk) do (clxs := apply(clSs, cli -> clV#cli);
     for clr from max(1, clk - cldk(clk) + 1) to clk do clQ = append(clQ, clEl(clxs, clr)));
  -- layer N_w, w = mu_1 - 1 (minimal generators: A, B nonempty, C = rest)
  clw := clmu#0 - 1; clLay := {};
  if clmu#0 >= 2 then (   -- for (1^l) the layer N_0 is omitted (redundant, INFORME_9, proved)
   if clmu#0 >= 2 or true then
    for cllab in toList((cln:0)..(cln:2)) do (
      clA := select(toList(0..cln-1), cli -> cllab#cli == 0); clB := select(toList(0..cln-1), cli -> cllab#cli == 1);
      if #clB >= 1 and #clB - #clA <= clw then clLay = append(clLay, product(toList(0..cln-1), cli -> if cllab#cli == 0 then (clV#cli)^(clq-1) else if cllab#cli == 2 then clV#cli else 1_clS)));
  );
  clt := clf + clell - 2; clFam := {};
  for clj from 0 to cln-1 do for cll from 0 to cln-1 do if clj != cll then (
    clrest := apply(select(toList(0..cln-1), cli -> cli != cll), cli -> clV#cli);
    clFam = append(clFam, (clV#clj)^(clq-clell+clpert) * sum(0..(clt//2), clk -> (clV#clj)^(2*clk) * clEl(clrest, clt - 2*clk))));
  clK := ideal(clQ) + ideal apply(clV, clv -> clv^clq) + (if #clLay > 0 then ideal clLay else ideal(0_clS)) + (if clpert >= 0 then ideal clFam else ideal(0_clS));
  cleq := (gens gb clK) == (gens gb clG);
  << "q=" << clq << " mu=" << toString clmu << " n=" << cln << " f=" << clf << " |W|=" << clwant << " : colength(G)=" << clcolG
     << (if clcolG == clwant then " CERTIFIED" else " *NOT CERTIFIED*") << " ; K==G as ideals: " << cleq
     << " ; colength(K)=" << degree(clS/clK) << " [" << (cpuTime()-clt0) << "s]" << endl << flush;
);
