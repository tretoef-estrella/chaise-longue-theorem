module

public import RequestProject.Bip.Peeling

/-!
# Item 1 of the Proofs of `q_any_bip.md`: Lemma 7.1 (peeling) for every box `q ≥ 2`

`q_any_bip.md`, **Proofs, "What the earlier proofs use", item 1** (*Lemma 7.1, peeling with the
box `q`*): the four parts of Lemma 7.1 of `q_bip_setting.md` (`Bip.Wslice_isIdeal`,
`Bip.Wslice_mono`, `Bip.finrank_eq_sum_Wslice`, `Bip.card_eq_sum_Zgt_bip`, stated there with
`q ≥ 3`) hold for every `q ≥ 2`.  The proofs are those of `RequestProject/Bip/Peeling.lean`: they
apply the peeling lemma of `q_peeling_lemma.md` with `q + 1` in place of `q`, which needs only
`q + 1 ≥ 3`, i.e. `q ≥ 2`.  The definitions (`Bip.R`, `Bip.Wslice`, …) are used unchanged.
-/

@[expose] public section

namespace BipAny

open Bip

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- `q_any_bip.md`, **Proofs, item 1** (Lemma 7.1 (i) of `q_bip_setting.md` for every `q ≥ 2`):
for `α ≥ 1`, an ideal `V` of `R_{α,β}` and `0 ≤ j ≤ q − 1`, the slice `W_j(V) ⊆ R_{α−1,β}` is an
ideal.  Same statement as `Bip.Wslice_isIdeal`, with `q ≥ 2` instead of `q ≥ 3`. -/
theorem Wslice_isIdeal (hq : 2 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) (j : ℕ)
    (hj : j ≤ q - 1) :
    ∃ I : Ideal (R F q (α - 1) β), (I : Set (R F q (α - 1) β)) = Wslice F q hα V j :=
  exists_ideal_map_castC _ _
    (Peel.W_isIdeal (q := q + 1) (by omega) (m := α + β) (by omega) V j (by omega))

/-- `q_any_bip.md`, **Proofs, item 1** (Lemma 7.1 (ii) of `q_bip_setting.md` for every `q ≥ 2`):
`W_j(V) ⊆ W_{j+1}(V)` for `0 ≤ j < q − 1` (for `q = 2` this is the single inclusion
`W_0 ⊆ W_1`).  Same statement as `Bip.Wslice_mono`, with `q ≥ 2` instead of `q ≥ 3`. -/
theorem Wslice_mono (hq : 2 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) (j : ℕ)
    (hj : j < q - 1) : Wslice F q hα V j ≤ Wslice F q hα V (j + 1) :=
  Submodule.map_mono (Peel.W_mono (q := q + 1) (by omega) (m := α + β) (by omega) V j (by omega))

/-- `q_any_bip.md`, **Proofs, item 1** (Lemma 7.1 (iii) of `q_bip_setting.md` for every `q ≥ 2`):
`dim V = Σ_{j=0}^{q−1} dim W_j(V)`.  Same statement as `Bip.finrank_eq_sum_Wslice`, with `q ≥ 2`
instead of `q ≥ 3`. -/
theorem finrank_eq_sum_Wslice (hq : 2 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) :
    Module.finrank F (V.restrictScalars F) =
      ∑ j ∈ Finset.range q, Module.finrank F (Wslice F q hα V j) := by
  rw [Peel.finrank_eq_sum (q := q + 1) (by omega) (m := α + β) (by omega) V,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ((castC F q (show α + β - 1 = α - 1 + β by omega)).toLinearEquiv.finrank_map_eq _).symm

/-- `q_any_bip.md`, **Proofs, item 1** (Lemma 7.1 (iv) of `q_bip_setting.md` for every `q ≥ 2`):
for a finite set `Ω` with `|Ω| = q` and `Z ⊆ Ω^α × Ω^β` (`α ≥ 1`),
`|Z| = Σ_{i=0}^{q−1} |Z_{>i}|`.  Same statement as `Bip.card_eq_sum_Zgt_bip`, with `q ≥ 2` instead
of `q ≥ 3`. -/
theorem card_eq_sum_Zgt_bip (hq : 2 ≤ q) {α β : ℕ} (hα : 1 ≤ α) {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = q) (Z : Finset ((Fin α → Ω) × (Fin β → Ω))) :
    Z.card = ∑ i ∈ Finset.range q, (Peel.Zgt (Z.map toTuple) i).card := by
  rw [← Finset.card_map toTuple,
    Peel.card_eq_sum_Zgt (q := q + 1) (by omega) (m := α + β) (by omega) (by omega),
    Nat.add_sub_cancel]

end BipAny

end
