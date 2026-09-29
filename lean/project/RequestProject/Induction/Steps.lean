module

public import RequestProject.Lifts.Main
public import RequestProject.Fibres.Main
public import RequestProject.Monotone.Main

/-!
# The steps of the induction of `q_induction.md`

This file proves the ingredients of the **Proof** of the Theorem of `q_induction.md`:
* the **Base `m = 0`** (`card_ZLam_zero_le`);
* **Step 1** of the step `m ≥ 1`: each layer `Λ_i` is a down-set of `Par_{m−1}`
  (`isDownSetPar_layer`);
* **Step 2**: the layers of `Z_Λ` are the `Z_{Λ_i}` (`Zgt_ZLam_eq_ZLam_layer`), using the fact
  that `λ(M') ∈ Par_{m−1}` (`resPart_mem_Par`).

Everything else is reused unchanged: `Par`, `IsDownSetPar`, `layer`, Step 0 (`opt_mem_Par`) and
the Proposition (`layer_subset_W`) of `q_P3_lifts.md` from `RequestProject/Lifts/`; the
Proposition `opt_weakDom_opt` of `q_P2_monotone_options.md`; `FibreSetting`, `resPart`, `FLam`,
`ZLam` and parts (i)–(iii) of `q_P1_fibres.md` from `RequestProject/Fibres/`; the ideals
`VLamAll` of `q_P3_identities.md`; and `C`, `W`, parts (iii) (`finrank_eq_sum`) and (iv)
(`card_eq_sum_Zgt`), `consTuple`, `fiber`, `Zgt` of `q_peeling_lemma.md`.
-/

@[expose] public section

namespace Induction

open ChainLemma ChainLemma.Partition Lifts Fibres Tight
open Peel hiding C

set_option synthInstance.maxHeartbeats 200000

/-- **Step 1** of the step `m ≥ 1` in the Proof of `q_induction.md` (the comparison of options):
if `λ ∈ Par_{m−1}`, `μ ∈ Par_{m−1}` and `λ ≼ μ`, then `F_Λ(λ) ≥ F_Λ(μ)` for every down-set `Λ`
of `Par_m` (with `h ≥ 1`, `L = 2h`).  By the Proposition of `q_P2_monotone_options.md`,
`opt_p(λ) ≼ opt_p(μ)`; all options lie in `Par_m` (Step 0 of `q_P3_lifts.md`), so
`opt_p(μ) ∈ Λ` implies `opt_p(λ) ∈ Λ`. -/
theorem FLam_le_FLam {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m) {Λ : Set Partition}
    (hΛ : IsDownSetPar h m Λ) {lam μ : Partition} (hlam : lam ∈ Par h (m - 1))
    (hμ : μ ∈ Par h (m - 1)) (hle : lam ≼ μ) : FLam h Λ μ ≤ FLam h Λ lam := by
  classical
  unfold FLam
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  obtain ⟨⟨hp1, hp2⟩, hpΛ⟩ := hp
  refine ⟨⟨hp1, hp2⟩, ?_⟩
  have hmem : lam.opt (2 * h) p ∈ Par h m := by
    have := opt_mem_Par hlam hp1 hp2
    rwa [Nat.sub_add_cancel hm] at this
  refine hΛ.2 _ _ hmem ?_ hpΛ
  exact opt_weakDom_opt h hh lam μ hlam.2.2 hμ.2.2 (by rw [hlam.2.1, hμ.2.1]) hle p hp1 hp2

/-- **Step 1** of the step `m ≥ 1` in the Proof of `q_induction.md`: for a down-set `Λ` of
`Par_m` (with `h ≥ 1`, `m ≥ 1`), each layer `Λ_i = {μ ∈ Par_{m−1} : F_Λ(μ) > i}` is a down-set of
`Par_{m−1}`. -/
theorem isDownSetPar_layer {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m) {Λ : Set Partition}
    (hΛ : IsDownSetPar h m Λ) (i : ℕ) : IsDownSetPar h (m - 1) (layer h m Λ i) :=
  ⟨fun _ hμ => hμ.1, fun _ _ hlam hle hμ =>
    ⟨hlam, lt_of_lt_of_le hμ.2 (FLam_le_FLam hh hm hΛ hlam hμ.1 hle)⟩⟩

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Step 2** of the step `m ≥ 1` in the Proof of `q_induction.md` (the fact
"`λ(M') ∈ Par_{m−1}` for every `M'`", credited there to part (i) of `q_P1_fibres.md`): for every
`M ∈ T^n`, `λ(M) ∈ Par_n`.  Part (i) of `q_P1_fibres.md` gives `ℓ(λ(M)) ≤ h` and
`|λ(M)| ≡ n (mod 2)`; the remaining condition `|λ(M)| ≤ n` holds because
`|λ(M)| = Σ_u (#{M_i = u} − #{M_i = −u}) ≤ Σ_u #{M_i = u} = n`. -/
theorem resPart_mem_Par (S : FibreSetting T h) {n : ℕ} (M : Fin n → T) :
    S.resPart M ∈ Par h n := by
  obtain ⟨h1, h2⟩ := resPart_len_le_and_size_mod S M
  refine ⟨?_, h2, h1⟩
  rw [FibreSetting.resPart, size_ofMultiset]
  calc (Finset.univ.val.map fun u => cnt M u - cnt M (S.neg u)).sum
      = ∑ u, (cnt M u - cnt M (S.neg u)) := rfl
    _ ≤ ∑ u, cnt M u := Finset.sum_le_sum fun u _ => Nat.sub_le _ _
    _ = n := by
      unfold cnt
      rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (M i))]
      simp

/-- **Step 2** of the step `m ≥ 1` in the Proof of `q_induction.md`: the layers of `Z_Λ` are the
`Z_{Λ_i}`, i.e. `Z_{>i} = Z_{Λ_i}` (for `m ≥ 1`), by part (iii) of `q_P1_fibres.md`
(`Z_{>i} = {M' : F_Λ(λ(M')) > i}`) and `λ(M') ∈ Par_{m−1}`. -/
theorem Zgt_ZLam_eq_ZLam_layer (S : FibreSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (Λ : Set Partition) (i : ℕ) :
    Zgt (S.ZLam m Λ) i = S.ZLam (m - 1) (layer h m Λ i) := by
  rw [Zgt_ZLam S hm]
  ext M'
  simp [FibreSetting.ZLam, layer, resPart_mem_Par S M']

/-- **Base `m = 0`** of the Proof of `q_induction.md`: for a down-set `Λ` of `Par_0` (with
`q ≥ 2`), `|Z_Λ| ≤ dim_F V_Λ`.  Here `T^0` has one element, so `|Z_Λ| ≤ 1`; if `Z_Λ ≠ ∅` then some
`λ ∈ Λ ⊆ Par_0` has `|λ| = 0`, i.e. `λ = ∅`, whose empty tight pattern has product `1`, so
`1 ∈ V_Λ` and `dim_F V_Λ ≥ 1`. -/
theorem card_ZLam_zero_le (F : Type*) [Field F] {q : ℕ} (hq : 2 ≤ q) (S : FibreSetting T h)
    (Λ : Set Partition) (hΛ : IsDownSetPar h 0 Λ) :
    (S.ZLam 0 Λ).card ≤ Module.finrank F ((VLamAll F q 0 Λ).restrictScalars F) := by
  haveI := nontrivial_C (F := F) (q := q) (m := 0) hq
  have hcard : (S.ZLam 0 Λ).card ≤ 1 :=
    (Finset.card_le_univ _).trans (by simp)
  rcases (S.ZLam 0 Λ).eq_empty_or_nonempty with he | ⟨M, hM⟩
  · simp [he]
  refine hcard.trans ?_
  have hlam : S.resPart M ∈ Λ := by
    classical
    exact (Finset.mem_filter.1 hM).2
  set lam := S.resPart M
  have hsize : lam.size = 0 := by have := (hΛ.1 hlam).1; omega
  have hparts : lam.parts = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have h0 := lam.pos x hx
    have := List.le_sum_of_mem hx
    rw [← Partition.size, hsize] at this
    omega
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
  have h1 : (1 : Peel.C F q 0) ∈ VLamAll F q 0 Λ := by
    have hprod : TP.prod F q = 1 := by simp [TightPattern.prod, TP, hrow]
    exact hprod ▸ Ideal.subset_span ⟨lam, hlam, TP, rfl⟩
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  have : (1 : Peel.C F q 0) ∈ (VLamAll F q 0 Λ).restrictScalars F := h1
  rw [hbot, Submodule.mem_bot] at this
  exact one_ne_zero this

end Induction

end
