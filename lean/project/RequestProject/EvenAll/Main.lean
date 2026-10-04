module

public import RequestProject.EvenAll.PartA
public import RequestProject.EvenAll.PartBC
public import RequestProject.EvenAll.PartD
public import RequestProject.EvenAll.PartE
public import RequestProject.EvenAll.Checks

/-!
# `q_even_assembly.md`: Main Theorem′ for every even degree (paper v11 Theorem 9.11), for every
`m ≥ 1`, and Corollary 9.12

This file imports every file of `RequestProject/EvenAll/`:
* Part A (`PartA.lean`): (A1) `EvenAll.A1`, (A2) `EvenAll.A2`, `A2_even`, `A2_odd`,
  (A3) `EvenAll.A3` (the hypothesis `H(m, k)` for every even `m ≥ 2`);
* Parts B and C (`PartBC.lean`): (B1) `EvenAll.B1`, (B2) `EvenAll.B2` (Theorem 9.11),
  (C1) `EvenAll.Qall`, (C2) `EvenAll.mainTheorem'` (Main Theorem′ for every `m ≥ 1`);
* Part D (`PartD.lean`): (D1) `EvenAll.D1_NS`, `D1_Nbal`, (D2) `EvenAll.D2`
  (Corollary 9.12 (i));
* Part E (`PartE.lean`): (E1) `EvenAll.E1` (Corollary 9.12 (ii)), (E2) `EvenAll.E2`
  (Corollary 7.8), both from `EvenAll.E_prime` and `EvenAll.bip_of_setting`;
* the checks (`Checks.lean`).

Not in Lean (and not claimed): the topology, i.e. the passage from Main Theorem′ to the homology of
the Fermat variety.
-/
