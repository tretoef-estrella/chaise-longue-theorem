module

public import RequestProject.OddEquality.Checks
public import RequestProject.OddEquality.PartC3

/-!
# `q_oddbox_equality.md`: the equality at the odd box (paper v11 Lemma 8.12, Corollary 8.13)

Summary of the formalization (namespace `OddEquality`), `q = 2h + 2` (box `r = 2h + 1`),
`N = 2k + 2`:

* **Part A** (`PartA.lean`): `A1` (`ℳ = OddPatterns.VSAll F h N {(∅, false)}`), `A2`
  (`Q^e_k(q) ≤ dim ℳ`), `theta`, `A3` (`θ(ι g · f) = g · θ f`), `A4` (`θ(D_{P_J}) = D_J`), `A5`
  (`dim (D_J) ≤ dim ℳ`).
* **Part B** (`PartB.lean`): `pairing`, `pairing_injective`, `B1` (any box `q ≥ 2`, any subspace),
  `B2_pair`, `B2`, `B3`.
* **Part C** (`PartC.lean`): `top_mem_IPS_sup` ((C3), any finite `T ⊆ F` with `|T| = r`, `−T = T`),
  `C1`, `C4`, `C5` (any field), `pointedTQ`, `card_Gamma` ((C2) over `ℚ`), `partC`;
  `PartC3.lean`: `C3_ideal`, `C3_top` (the two equalities of (C3)).
* **Part D** (`PartD.lean`, `IntegralGen.lean`): `D1` (every field), `D2_DJ`, `D2_M` (freeness over
  `ℤ`), `partB_attained`. (D3) is not formalized.
* **Checks** (`Checks.lean`).
-/
