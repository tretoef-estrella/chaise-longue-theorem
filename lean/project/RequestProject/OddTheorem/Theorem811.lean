module

public import RequestProject.OddTheorem.Prop810

/-!
# Part T of `q_oddbox_theorem.md`: Theorem 8.11 (interlaced down-set theorem)

This file formalizes **(T) Theorem 8.11** of `q_oddbox_theorem.md`: `|Z_Λ| ≤ dim_F V_Λ` for every
interlaced pair `Λ`, by induction on the level `m`, as `Induction.finrank_VLamAll_ge_card_ZLam`.
-/

@[expose] public section

namespace OddTheorem

open Peel hiding C
open Tight ChainLemma OddShapes OddPatterns

set_option synthInstance.maxHeartbeats 200000

/-- Auxiliary for **(T)** of `q_oddbox_theorem.md` (the base `m = 0`): a shape of level `0` is
`(∅, false)`, i.e. its partition has no rows and it is unmarked. -/
theorem parts_eq_nil_of_mem_Sh_zero {h : ℕ} {s : Shape} (hs : s ∈ Sh h 0) :
    s.1.parts = [] ∧ s.2 = false := by
  obtain ⟨-, h2, -⟩ := hs
  have hsize : s.1.size = 0 := by omega
  refine ⟨?_, ?_⟩
  · rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have h0 := s.1.pos x hx
    have := List.le_sum_of_mem hx
    rw [← Partition.size, hsize] at this
    omega
  · cases hb : s.2 with
    | false => rfl
    | true => rw [hb] at h2; simp at h2

/-- **(T)**, the base `m = 0`, of `q_oddbox_theorem.md`: `Sh h 0 = {(∅, false)}`, so `|Z_Λ| ≤ 1`;
if `Z_Λ` is non-empty then `(∅, false) ∈ Λ`, the empty tight pattern has product `1`, so
`1 ∈ V_Λ` and `dim V_Λ ≥ 1`. -/
theorem card_ZS_zero_le (F : Type*) [Field F] {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}
    (S : OddSetting T h) (Lam : Set Shape) (hΛ : IsInterlaced h 0 Lam) :
    (ZS S 0 Lam).card ≤ Module.finrank F ((VSAll F h 0 Lam).restrictScalars F) := by
  haveI := nontrivial_C (F := F) (q := 2 * h + 2) (m := 0) (by omega)
  have hcard : (ZS S 0 Lam).card ≤ 1 :=
    (Finset.card_le_univ _).trans (by simp)
  rcases (ZS S 0 Lam).eq_empty_or_nonempty with he | ⟨M, hM⟩
  · simp [he]
  refine hcard.trans ?_
  have hsl : S.shape M ∈ Lam := by
    classical
    exact (Finset.mem_filter.1 hM).2
  obtain ⟨hparts, hmark⟩ := parts_eq_nil_of_mem_Sh_zero (hΛ.1 hsl)
  set lam := (S.shape M).1
  have hlam : (lam, false) ∈ Lam := by
    have : S.shape M = (lam, false) := Prod.ext rfl hmark
    rw [← this]; exact hsl
  have hsize : lam.size = 0 := by simp [Partition.size, hparts]
  have hrow : lam.row 1 = 0 := by simp [Partition.row, hparts]
  let TP : TightPattern lam (Finset.univ : Finset (Fin 0)) :=
    { pairs := ∅
      blocks := fun _ => ∅
      size_le := by simp [hsize]
      even_sub := by simp [hsize]
      card_pairs := by simp [hsize]
      card_pair := by simp
      pairs_disjoint := by simp
      card_block := by simp [hrow]
      blocks_disjoint := by simp [hrow]
      pairs_blocks_disjoint := by simp
      cover := by ext x; exact x.elim0 }
  have h1 : (1 : Peel.C F (2 * h + 2) 0) ∈ VSAll F h 0 Lam := by
    have hprod : TP.prod F (2 * h + 2) = 1 := by simp [TightPattern.prod, TP, hrow]
    exact hprod ▸ B4_tight (F := F) (h := h) hlam TP
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  have : (1 : Peel.C F (2 * h + 2) 0) ∈ (VSAll F h 0 Lam).restrictScalars F := h1
  rw [hbot, Submodule.mem_bot] at this
  exact one_ne_zero this

/-- **(T)**, the step `m ≥ 1`, of `q_oddbox_theorem.md`: assuming `|Z_{Λ'}| ≤ dim V_{Λ'}` for all
interlaced `Λ'` of level `m − 1`,
`|Z_Λ| = Σ_{i<2h+1} |Z_{Λ_i}| ≤ Σ_i dim V_{Λ_i} ≤ Σ_i dim W_{2h−i}(V_Λ) = dim V_Λ`, by
`OddLayers.card_ZS_eq_sum`, the induction hypothesis (`OddLayers.isInterlaced_layerS`),
Proposition 8.10 and `Peel.finrank_eq_sum` (reflected). -/
theorem card_ZS_le_step (F : Type*) [Field F] {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}
    (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ Lam' : Set Shape, IsInterlaced h (m - 1) Lam' →
      (ZS S (m - 1) Lam').card ≤ Module.finrank F ((VSAll F h (m - 1) Lam').restrictScalars F))
    (Lam : Set Shape) (hΛ : IsInterlaced h m Lam) :
    (ZS S m Lam).card ≤ Module.finrank F ((VSAll F h m Lam).restrictScalars F) := by
  have hh := S.one_le
  rw [OddLayers.card_ZS_eq_sum S hm, finrank_eq_sum (q := 2 * h + 2) (by omega) hm,
    show 2 * h + 2 - 1 = 2 * h + 1 by omega,
    ← Finset.sum_range_reflect (fun j => Module.finrank F (W hm (VSAll F h m Lam) j))]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show 2 * h + 1 - 1 - i = 2 * h - i by omega]
  refine (ih _ (OddLayers.isInterlaced_layerS hh hm hΛ i)).trans ?_
  have hsub : (VSAll F h (m - 1) (OddLayers.layerS h m Lam i)).restrictScalars F ≤
      W hm (VSAll F h m Lam) (2 * h - i) := fun x hx =>
    prop810 hh hm hΛ (by omega) hx
  exact Submodule.finrank_mono hsub

/-- **(T) Theorem 8.11** (interlaced down-set theorem) of `q_oddbox_theorem.md`: for every field
`F`, every finite type `T` with decidable equality, every `S : OddSetting T h`, every `m` and every
`Λ` interlaced of level `m`: `|Z_Λ| ≤ dim_F V_Λ`. (Induction on `m`, generalizing `Λ`; the base
is `card_ZS_zero_le` and the step is `card_ZS_le_step`.) -/
theorem theorem811 (F : Type*) [Field F] {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}
    (S : OddSetting T h) (m : ℕ) (Lam : Set Shape) (hΛ : IsInterlaced h m Lam) :
    (ZS S m Lam).card ≤ Module.finrank F ((VSAll F h m Lam).restrictScalars F) := by
  induction m generalizing Lam with
  | zero => exact card_ZS_zero_le F S Lam hΛ
  | succ n ih => exact card_ZS_le_step F S (m := n + 1) (by omega) ih Lam hΛ

end OddTheorem
