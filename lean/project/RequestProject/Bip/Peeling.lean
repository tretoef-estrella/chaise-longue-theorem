module

public import RequestProject.Bip.Defs

/-!
# Lemma 7.1 of `q_bip_setting.md` (peeling with the box `q`)

Parts (i)–(iv) of **Lemma 7.1** of `q_bip_setting.md`, obtained, as in the file, from parts
(i)–(iv) of the Lemma of `q_peeling_lemma.md` (`Peel.W_isIdeal`, `Peel.W_mono`,
`Peel.finrank_eq_sum`, `Peel.card_eq_sum_Zgt`) applied with `q + 1` in place of `q`, on
`α + β` variables, peeling the first one `y_1 = x_1`.
-/

@[expose] public section

namespace Bip

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {q : ℕ}

/-- Transport of "is an ideal" along the renaming isomorphism `castC` (auxiliary for
**Lemma 7.1 (i)** of `q_bip_setting.md`). -/
theorem exists_ideal_map_castC {m n : ℕ} (h : m = n) (W : Submodule F (Peel.C F (q + 1) m))
    (hW : ∃ I : Ideal (Peel.C F (q + 1) m), (I : Set (Peel.C F (q + 1) m)) = W) :
    ∃ I : Ideal (Peel.C F (q + 1) n),
      (I : Set (Peel.C F (q + 1) n)) = W.map (castC F q h).toLinearMap := by
  subst h
  obtain ⟨I, hI⟩ := hW
  refine ⟨I, ?_⟩
  rw [hI]
  ext v
  simp [castC]

/-- **Lemma 7.1 (i)** of `q_bip_setting.md`: for `α ≥ 1`, an ideal `V` of `R_{α,β}` and
`0 ≤ j ≤ q − 1`, the slice `W_j(V) ⊆ R_{α−1,β}` is an ideal ("is an ideal" means that some ideal
of `R_{α−1,β}` has exactly `W_j(V)` as underlying set).  The Setting's hypothesis `q ≥ 3` is kept
(`q` odd is not needed). -/
theorem Wslice_isIdeal (hq : 3 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) (j : ℕ)
    (hj : j ≤ q - 1) :
    ∃ I : Ideal (R F q (α - 1) β), (I : Set (R F q (α - 1) β)) = Wslice F q hα V j :=
  exists_ideal_map_castC _ _
    (Peel.W_isIdeal (q := q + 1) (by omega) (m := α + β) (by omega) V j (by omega))

/-- **Lemma 7.1 (ii)** of `q_bip_setting.md`: `W_j(V) ⊆ W_{j+1}(V)` for `0 ≤ j < q − 1`.  The
Setting's hypothesis `q ≥ 3` is kept (`q` odd is not needed). -/
theorem Wslice_mono (hq : 3 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) (j : ℕ)
    (hj : j < q - 1) : Wslice F q hα V j ≤ Wslice F q hα V (j + 1) :=
  Submodule.map_mono (Peel.W_mono (q := q + 1) (by omega) (m := α + β) (by omega) V j (by omega))

/-- **Lemma 7.1 (iii)** of `q_bip_setting.md`: `dim V = Σ_{j=0}^{q−1} dim W_j(V)`, where `dim V` is
the `F`-dimension of the ideal `V` of `R_{α,β}` and the sum over `j = 0, …, q−1` is over
`Finset.range q`.  The Setting's hypothesis `q ≥ 3` is kept (`q` odd is not needed). -/
theorem finrank_eq_sum_Wslice (hq : 3 ≤ q) {α β : ℕ} (hα : 1 ≤ α) (V : Ideal (R F q α β)) :
    Module.finrank F (V.restrictScalars F) =
      ∑ j ∈ Finset.range q, Module.finrank F (Wslice F q hα V j) := by
  rw [Peel.finrank_eq_sum (q := q + 1) (by omega) (m := α + β) (by omega) V,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact ((castC F q (show α + β - 1 = α - 1 + β by omega)).toLinearEquiv.finrank_map_eq _).symm

/-- **Lemma 7.1 (iv)** of `q_bip_setting.md`: for a finite set `Ω` with `|Ω| = q` and
`Z ⊆ Ω^α × Ω^β` (`α ≥ 1`), `|Z| = Σ_{i=0}^{q−1} |Z_{>i}|`.  Here the fibres
`F(M') = {u ∈ Ω : (u, M') ∈ Z}` over the tails `M'` (all coordinates but `ξ_1`) and the sets
`Z_{>i} = {M' : |F(M')| > i}` are `Peel.fiber` and `Peel.Zgt` of `q_peeling_lemma.md`, computed on
the image of `Z` under `(ξ, η) ↦ (ξ_1, …, ξ_α, η_1, …, η_β) ∈ Ω^{α+β}` (`toTuple`); the sum is
over `Finset.range q`.  The Setting's hypothesis `q ≥ 3` is kept (`q` odd is not needed). -/
theorem card_eq_sum_Zgt_bip (hq : 3 ≤ q) {α β : ℕ} (hα : 1 ≤ α) {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = q) (Z : Finset ((Fin α → Ω) × (Fin β → Ω))) :
    Z.card = ∑ i ∈ Finset.range q, (Peel.Zgt (Z.map toTuple) i).card := by
  rw [← Finset.card_map toTuple,
    Peel.card_eq_sum_Zgt (q := q + 1) (by omega) (m := α + β) (by omega) (by omega),
    Nat.add_sub_cancel]

end Bip

end
