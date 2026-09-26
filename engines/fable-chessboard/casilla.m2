-- casilla.m2 (auditor, 2026-09-21). Checks the CASILLA THEOREMS in small cells.
-- EVEN: J_1 = pi(I^(2k+2) : x_{2k+1}) == I^(2k+1) + M_k.   ODD: J'_1 = pi(I^(2k+1) : x_{2k}) == I^(2k) + (y_0...y_{2k-1}) + M'_{j<=2}.
-- M = monomials x_C x_A^(q-1), A,B,C partition of the variables of the target ring, |A|=|B|=j>=1.
-- Estimate: < 1 min, < 400 MB.
cells = {(1,9),(2,3),(2,9),(3,3)};
for par in {0,1} do for c in cells do (
  k := c#0; q := c#1; n := if par == 0 then 2*k+2 else 2*k+1;
  S := ZZ/3[x_0..x_(n-1)];
  el := j -> sum(subsets(gens S, j), product);
  I := ideal(apply(select(toList(1..n), j -> odd j), j -> el j)) + ideal(apply(gens S, v -> v^q));
  T := ZZ/3[y_0..y_(n-2)];
  f := map(T, S, (gens T) | {0_T});
  J1 := f(I : x_(n-1)); J0 := f(I);
  idx := toList(0..n-2); Mg := {};
  jmax := if par == 0 then k else min(2, k-1);
  for j from 1 to jmax do for A in subsets(idx, j) do (rest := toList(set idx - set A);
      for B in subsets(rest, j) do Mg = append(Mg, product(toList(set rest - set B), i -> y_i)*product(A, i -> y_i^(q-1))));
  K := J0 + (if #Mg > 0 then ideal Mg else ideal 0_T) + (if par == 1 then ideal product gens T else ideal 0_T);
  << (if par==0 then "EVEN" else "ODD ") << " k=" << k << " q=" << q << " dim J_1=" << degree(T^1/J1) << " dim K=" << degree(T^1/K) << " equal:" << (K==J1) << endl << flush;
);
<< "FIN-OK" << endl; exit 0;
