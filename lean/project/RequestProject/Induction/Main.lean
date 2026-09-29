module

public import RequestProject.Induction.Steps

/-!
# The induction `dim V_Λ ≥ |Z_Λ|` (`q_induction.md`)

Formalization of the **Theorem** of `q_induction.md`.

**Setting** of `q_induction.md`: `F` is a field, `q ≥ 3` is odd, `h = (q − 1)/2`, and `T` is a
finite set with a fixed-point-free involution and `|T| = 2h = q − 1`; this is
`S : Fibres.FibreSetting T ((q - 1) / 2)` of `q_P1_fibres.md`.  For `m ≥ 0` and a down-set `Λ`
of `Par_m` (`Lifts.IsDownSetPar ((q - 1) / 2) m Λ`, exactly the notion of `q_P3_lifts.md`:
`Λ ⊆ Par_m` and closed under `≼` *inside* `Par_m`), `Z_Λ = {M ∈ T^m : λ(M) ∈ Λ}` is
`S.ZLam m Λ` and `V_Λ ⊆ C_m` is `Tight.VLamAll F q m Λ`.  As in part (iii) of
`q_peeling_lemma.md`, `dim_F V_Λ` is the `F`-dimension of the ideal `V_Λ` regarded as an
`F`-subspace of `C_m` (`(VLamAll F q m Λ).restrictScalars F`).

The ingredients (Base, Steps 1 and 2) are in `RequestProject/Induction/Steps.lean`; Step 3 and
the induction are here.
-/

@[expose] public section

namespace Induction

open ChainLemma Lifts Fibres Tight
open Peel hiding C

set_option synthInstance.maxHeartbeats 200000

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **Step 3** ("Chain of (in)equalities") of the step `m ≥ 1` in the Proof of `q_induction.md`:
assuming the induction hypothesis `dim V_{Λ'} ≥ |Z_{Λ'}|` for all down-sets `Λ'` of `Par_{m−1}`,
for every down-set `Λ` of `Par_m`,
`dim V_Λ = Σ_{i=0}^{q−2} dim W_{q−2−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = Σ_i |Z_{>i}| = |Z_Λ|`,
by part (iii) of `q_peeling_lemma.md` (reindexed by `j = q − 2 − i`), the Proposition of
`q_P3_lifts.md`, the induction hypothesis (applicable by Step 1), Step 2, and part (iv) of
`q_peeling_lemma.md` (`|T| = q − 1`). -/
theorem card_ZLam_le_step (F : Type*) [Field F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (S : FibreSetting T ((q - 1) / 2)) {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ Λ' : Set Partition, IsDownSetPar ((q - 1) / 2) (m - 1) Λ' →
      (S.ZLam (m - 1) Λ').card ≤ Module.finrank F ((VLamAll F q (m - 1) Λ').restrictScalars F))
    (Λ : Set Partition) (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    (S.ZLam m Λ).card ≤ Module.finrank F ((VLamAll F q m Λ).restrictScalars F) := by
  have hT : Fintype.card T = q - 1 := by
    rw [S.card_eq]; obtain ⟨k, rfl⟩ := hodd; omega
  have hh : 1 ≤ (q - 1) / 2 := by omega
  rw [card_eq_sum_Zgt hq hm hT, finrank_eq_sum hq hm,
    ← Finset.sum_range_reflect (fun j => Module.finrank F (W hm (VLamAll F q m Λ) j))]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Zgt_ZLam_eq_ZLam_layer S hm, show q - 1 - 1 - i = q - 2 - i by omega]
  refine (ih _ (isDownSetPar_layer hh hm hΛ i)).trans ?_
  have hsub : (VLamAll F q (m - 1) (layer ((q - 1) / 2) m Λ i)).restrictScalars F ≤
      W hm (VLamAll F q m Λ) (q - 2 - i) := fun x hx =>
    layer_subset_W hq hodd hm Λ hΛ i (by omega) hx
  exact Submodule.finrank_mono hsub

/-- **Theorem** of `q_induction.md`: let `F` be a field, `q ≥ 3` odd, `h = (q − 1)/2`, and `T` a
finite set with a fixed-point-free involution and `|T| = 2h` (the **Setting**, bundled in `S`).
For every `m ≥ 0` and every down-set `Λ` of `Par_m` (not necessarily a global down-set):
`dim_F V_Λ ≥ |Z_Λ|`.

The proof is the **Proof** of `q_induction.md`: induction on `m` with `F`, `q`, `T` fixed; the
**Base `m = 0`** is `card_ZLam_zero_le` and the **Step `m ≥ 1`** is `card_ZLam_le_step`
(Steps 1–3). -/
theorem finrank_VLamAll_ge_card_ZLam (F : Type*) [Field F] {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (S : FibreSetting T ((q - 1) / 2)) (m : ℕ) (Λ : Set Partition)
    (hΛ : IsDownSetPar ((q - 1) / 2) m Λ) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) ≥ (S.ZLam m Λ).card := by
  induction m generalizing Λ with
  | zero => exact card_ZLam_zero_le F (by omega) S Λ hΛ
  | succ n ih => exact card_ZLam_le_step F hq hodd S (m := n + 1) (by omega) ih Λ hΛ

end Induction

end
