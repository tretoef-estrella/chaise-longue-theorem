-- regla259 (Grepy el Lector): are the LEDGER rows TRUE?  For a parent (mu,n) with anchor S:
--   G := gr I(W_S(n)) (true casilla); z := last variable; R_a := pi_z(G : z^a), a = 0..q-1;
--   children: W_{S u {v}}(n-1), v in F_q;  test  R_a == gr I(W_child(a))  AS IDEALS,
--   children sorted by fibre size (largest to a = 0), ties resolved by the dictionary type.
clEl = (clv, clr) -> (if clr < 0 then return 0; if clr == 0 then return 1; if clr > #clv then return 0; sum(subsets(clv, clr), clt -> product clt));
clTop = clg -> part((degree clg)#0, clg);
clTrue = (clS, clAnch) -> (  -- true casilla over ring clS (all its variables are y)
  clV := gens clS; clM := #clAnch; cln := #clV;
  clRel := for clj from 1 to cln+clM list (if even clj then continue; sum(0..clM, clr -> clEl(clAnch, clr) * clEl(clV, clj-clr)));
  clI := ideal clRel + ideal apply(clV, clv -> clv^clQQ - clv);
  ideal apply(flatten entries gens gb clI, clTop));
clQQ = 9; clKK = GF(clQQ, Variable=>cla);
clRows = (clEx, cln, clname) -> (
  clAnch0 := apply(clEx, cle -> cla^cle);
  clS := clKK[clx_1..clx_cln, MonomialOrder=>GRevLex];
  clAnch := apply(clAnch0, clu -> sub(clu, clS));
  clG := clTrue(clS, clAnch);
  clT := clKK[clx_1..clx_(cln-1), MonomialOrder=>GRevLex];
  clz := clS_(cln-1);
  clpi := map(clT, clS, (gens clT) | {0_clT});
  -- children by value v
  clvals := {0_clKK} | apply(toList(0..clQQ-2), cli -> cla^cli);
  clCh := apply(clvals, clv -> (clA := apply(clAnch0, clu -> sub(clu, clT)) | {sub(clv, clT)}; clC := clTrue(clT, clA); (degree(clT/clC), clC, clv)));
  clCh = reverse sort(clCh, clc -> clc#0);   -- largest fibre first
  clok := 0; clcols := {};
  for cla0 from 0 to clQQ-1 do (
     clR := clpi(quotient(clG, clz^cla0)) + ideal(0_clT);
     clcr := degree(clT/clR); clcols = append(clcols, clcr);
     -- find a child with the same colength whose casilla equals the row
     clm := select(clCh, clc -> clc#0 == clcr and (gens gb clc#1) == (gens gb clR));
     if #clm > 0 then clok = clok + 1 else << "   row " << cla0 << " colength " << clcr << " : NO child casilla equals it" << endl << flush;
  );
  << clname << " n=" << cln << " |W|=" << degree(clS/clG) << " rows colengths " << toString clcols << " sum " << sum clcols
     << " ; child fibres " << toString apply(clCh, clc -> clc#0) << " ; rows == some child true casilla: " << clok << "/" << clQQ << endl << flush;
);
