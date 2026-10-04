module

public import RequestProject.EvenOne.Main
public import RequestProject.EvenAssembly.Main

/-!
# Part A of `q_even_assembly.md`: the hypothesis `H(m, k)` for every even `m`

* **(A1)** `EvenAll.A1`: `ColDecomp.idealI S k = ColUpper.IK F S.m k`.
* **(A2)** `EvenAll.A2`, `EvenAll.A2_even`, `EvenAll.A2_odd`: for every `ColSetting S`,
  `finrank F (idealI S k) = card (closedT negT (2k+2))`, hence `= QkEven k S.m` for even `S.m`
  and `= TheoremB.Qk k S.m` for odd `S.m`.
* **(A3)** `EvenAll.A3`: `EvenAssembly.HypH m k` for every even `m ≥ 2` and every `k`.
-/

@[expose] public section

namespace EvenAll

open ColSplit ColUpper ColDecomp EvenCount

open scoped Classical

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- **Part A, (A1)** of `q_even_assembly.md`: for every `ColSetting S` over `F` and every `k`,
`ColDecomp.idealI S k = ColUpper.IK F S.m k`: both are the span of the same family, since
`ColSurv.psi S k J = psiG F S.m J` (`ColUpper.psi_eq_psiG`). -/
theorem A1 (S : ColSetting F) (k : ℕ) : idealI S k = IK F S.m k := rfl

/-- **Part A, (A2)** of `q_even_assembly.md` (**equality for every `ColSetting`**): for every
`ColSetting S` over `F` and every `k`,
`finrank F ((idealI S k).restrictScalars F) = card (closedT (negT S) (2k+2))`.
(`≥` is `EvenOne.E3`; `≤` is `EvenCount.finrank_IK_le_even` for even `S.m` (with `2 ≤ S.m`) and
`ColUpper.finrank_IK_le` for odd `S.m`, with (A1) and `EvenColours.C4`, `C4_even`, `C4_odd`.) -/
theorem A2 (S : ColSetting F) (k : ℕ) :
    Module.finrank F ((idealI S k).restrictScalars F) =
      (EvenColours.closedT (EvenColours.negT S) (2 * k + 2)).card := by
  obtain ⟨R, hR⟩ := EvenBlocks.exists_isReps2 (S := S)
  refine le_antisymm ?_ (EvenOne.E3 S k).1
  rw [A1]
  rcases Nat.even_or_odd S.m with h | h
  · rw [← EvenColours.C4 hR k, EvenColours.C4_even hR k h]
    exact finrank_IK_le_even F h (EvenColours.two_le_m S) k
  · rw [← EvenColours.C4 hR k, EvenColours.C4_odd hR k h]
    exact finrank_IK_le F h k

/-- **Part A, (A2)** of `q_even_assembly.md`, even `S.m`: if `Even S.m`, then
`finrank F ((idealI S k).restrictScalars F) = EvenCount.QkEven k S.m`. -/
theorem A2_even (S : ColSetting F) (k : ℕ) (h : Even S.m) :
    Module.finrank F ((idealI S k).restrictScalars F) = QkEven k S.m := by
  obtain ⟨R, hR⟩ := EvenBlocks.exists_isReps2 (S := S)
  rw [A2, ← EvenColours.C4 hR k, EvenColours.C4_even hR k h]

/-- **Part A, (A2)** of `q_even_assembly.md`, odd `S.m`: if `Odd S.m`, then
`finrank F ((idealI S k).restrictScalars F) = TheoremB.Qk k S.m`. -/
theorem A2_odd (S : ColSetting F) (k : ℕ) (h : Odd S.m) :
    Module.finrank F ((idealI S k).restrictScalars F) = TheoremB.Qk k S.m := by
  obtain ⟨R, hR⟩ := EvenBlocks.exists_isReps2 (S := S)
  rw [A2, ← EvenColours.C4 hR k, EvenColours.C4_odd hR k h]

/-- **Part A, (A3)** of `q_even_assembly.md` (**the hypothesis `H(m, k)`**): for every even
`m ≥ 2` and every `k`, `EvenAssembly.HypH m k`. (For a prime `p ∣ m`, write `m = p^v·r` with
`v ≥ 1` and `p ∤ r`, take `S := EvenBlocks.algClosureSetting p v _ r _ _` over
`K = AlgebraicClosure (ZMod p)` (so `S.m = m`); by (A1), (A2) and
`ColUpper.finrank_IK_eq_rankOver`, `rankOver K (intMatU m k) = QkEven k m`, and
`rankOver K = rankOver (ZMod p)` by `ColAssembly.rankOver_eq_rankOver_zmod` (which is
`ColAssembly.rank_map_algebraMap` for the extension `ZMod p → K`).) -/
theorem A3 {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) : EvenAssembly.HypH m k := by
  intro p hp hpm
  haveI := Fact.mk hp
  obtain ⟨v, r, hr, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.ne_one
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; omega
    · exact h0
  have hv : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · subst h0
      rw [pow_zero, one_mul] at hm
      exact absurd (hm ▸ hpm) hr
    · exact h0
  let S := EvenBlocks.algClosureSetting p v hv r hr1 hr
  have hSm : S.m = m := by rw [hm]; rfl
  have h := A2_even S k (hSm ▸ heven)
  rw [A1, finrank_IK_eq_rankOver (by rw [hSm]; omega), hSm] at h
  rw [← ColAssembly.rankOver_eq_rankOver_zmod (AlgebraicClosure (ZMod p)) p]
  exact h

end EvenAll

end
