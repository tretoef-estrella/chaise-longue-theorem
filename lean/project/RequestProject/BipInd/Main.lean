module

public import RequestProject.BipInd.Swap
public import RequestProject.BipP2.Main
public import RequestProject.BipP3.Main

/-!
# Theorem 7.6 and Theorem C of `q_bip_induction.md`

Formalization of **Theorem 7.6** (the bipartite down-set theorem) and **Theorem C** (the
bipartite count) of `q_bip_induction.md`, with the proofs of the file:

* **Proof of Theorem 7.6**: induction on `n = α + β` — the base `n = 0` (`card_ZLam_le_base`),
  the step for `α ≥ 1` peeling `w = x_1` (`card_ZLam_le_of_peel`, using Lemma 7.1 (iii), (iv) of
  `q_bip_setting.md`, Lemma 7.3 (ii) of `q_bip_options.md`, Proposition 7.4 (ii) of
  `q_bip_P2.md` and Proposition 7.5 of `q_bip_P3.md`), and the step for `α = 0` by the swap
  (Lemma S, `RequestProject/BipInd/Swap.lean`);
* **Proof of Theorem C**: Lemma 7.2 (i), (ii), (iii) of `q_bip_setting.md` and Theorem 7.6.

Dimensions are `Module.finrank F` of the ideals regarded as `F`-subspaces (`restrictScalars F`),
as in `Bip.finrank_eq_sum_Wslice`.
-/

@[expose] public section

open MvPolynomial

namespace Bip

open ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable (F : Type*) [Field F] {q : ℕ}

/-- `R_{0,0} = F` is not the zero ring (used in the base `n = 0` of the **Proof of Theorem 7.6**
of `q_bip_induction.md`). -/
theorem nontrivial_R_zero : Nontrivial (R F q 0 0) := by
  have h : Peel.powIdeal F (q + 1) (0 + 0) = ⊥ := by
    unfold Peel.powIdeal
    haveI : IsEmpty (Fin (0 + 0)) := ⟨fun i => Fin.elim0 i⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
  exact Ideal.Quotient.nontrivial_iff.2 (by rw [h]; exact bot_ne_top)

/-- **Proof of Theorem 7.6** of `q_bip_induction.md`, base `n = 0`: for every set `Λ`,
`|Z_Λ| ≤ dim V_Λ` in `R_{0,0}`.  (`Z_Λ` has at most the single point `(∅, ∅)`, whose shape is
`(∅, ∅)`; if it lies in `Z_Λ`, then `V_Λ ⊇ V_{{(∅,∅)}} = I^{bal}_0 = R_{0,0}`, of dimension `1`.) -/
theorem card_ZLam_le_base {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q)
    (Λ : Set (Partition × Partition)) :
    (ZLam Ω 0 0 Λ).card ≤ Module.finrank F ((VLamB F q 0 0 Λ).restrictScalars F) := by
  classical
  rcases Finset.eq_empty_or_nonempty (ZLam Ω 0 0 Λ) with h | ⟨p, hp⟩
  · simp [h]
  have hcard : (ZLam Ω 0 0 Λ).card ≤ 1 := by
    calc (ZLam Ω 0 0 Λ).card ≤ Fintype.card ((Fin 0 → Ω) × (Fin 0 → Ω)) :=
          Finset.card_le_univ _
      _ = 1 := by simp
  have hsh : shape p.1 p.2 = (Partition'.empty, Partition'.empty) := by
    refine Prod.ext ?_ ?_ <;> apply ChainLemma.Partition.ext <;>
      simp [shape, shapePlus, shapeMinus, Partition'.ofMultiset, Partition'.empty, cnt]
  have hmem : shape p.1 p.2 ∈ Λ := by
    simp only [ZLam, Finset.mem_filter] at hp
    exact hp.2
  have hsub : VLamB F q 0 0 {(Partition'.empty, Partition'.empty)} ≤ VLamB F q 0 0 Λ := by
    refine Ideal.span_mono ?_
    rintro _ ⟨lam, hl, T, rfl⟩
    refine ⟨lam, ?_, T, rfl⟩
    rw [Set.mem_singleton_iff.1 hl, ← hsh]
    exact hmem
  rw [(lemma72_i F hΩ 0).2.1] at hsub
  have h1 : (1 : R F q 0 0) ∈ Ibal F q 0 := Ideal.subset_span ⟨1, by simp⟩
  haveI := nontrivial_R_zero F (q := q)
  have hne : (VLamB F q 0 0 Λ).restrictScalars F ≠ ⊥ := by
    intro h
    have h1' : (1 : R F q 0 0) ∈ (VLamB F q 0 0 Λ).restrictScalars F := hsub h1
    rw [h] at h1'
    exact one_ne_zero ((Submodule.mem_bot F).1 h1')
  have hpos : 0 < Module.finrank F ((VLamB F q 0 0 Λ).restrictScalars F) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  omega

/-- **Proof of Theorem 7.6** of `q_bip_induction.md`, step `n ≥ 1`, case `α ≥ 1`: peeling
`w = x_1`, if `dim V_{Λ'} ≥ |Z_{Λ'}|` for every down-set `Λ'` of `BPar_q(α − 1, β)` (the induction
hypothesis), then `dim V_Λ ≥ |Z_Λ|` for every down-set `Λ` of `BPar_q(α, β)`:
`dim V_Λ = Σ_i dim W_{q−1−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = Σ_i |Z_{>i}| = |Z_Λ|`. -/
theorem card_ZLam_le_of_peel (hq : 3 ≤ q) (hodd : Odd q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (IH : ∀ Λ' : Set (Partition × Partition), IsDownSetB q (α - 1) β Λ' →
      (ZLam Ω (α - 1) β Λ').card ≤ Module.finrank F ((VLamB F q (α - 1) β Λ').restrictScalars F)) :
    (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  rw [card_eq_sum_Zgt_bip hq hα hΩ, finrank_eq_sum_Wslice hq hα,
    ← Finset.sum_range_reflect (fun j => Module.finrank F (Wslice F q hα (VLamB F q α β Λ) j)) q]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ q - 1 := by
    rw [Finset.mem_range] at hi
    omega
  rw [lemma73_ii_Zgt hq hΩ hα hΛ i,
    Finset.card_image_of_injective _ (tailToTuple_bijective hα).1]
  calc (ZLam Ω (α - 1) β (LamLayer q α β Λ i)).card
      ≤ Module.finrank F ((VLamB F q (α - 1) β (LamLayer q α β Λ i)).restrictScalars F) :=
        IH _ ((prop74_ii hq hα hΛ).2 i)
    _ ≤ Module.finrank F (Wslice F q hα (VLamB F q α β Λ) (q - 1 - i)) :=
        Submodule.finrank_mono fun g hg => BipP3.prop75 hq hodd hbin hα Λ hΛ i hi' hg

/-- **Theorem 7.6** of `q_bip_induction.md` (bipartite down-set theorem): let `F` be a field,
`q ≥ 3` odd with `C(q−1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`, and `Ω` a finite set with
`|Ω| = q`.  For all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`, `dim V_Λ ≥ |Z_Λ|`
(`dim` the `F`-dimension of the ideal `V_Λ ⊆ R_{α,β}`). -/
theorem thm76 (hq : 3 ≤ q) (hodd : Odd q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q) (α β : ℕ)
    (Λ : Set (Partition × Partition)) (hΛ : IsDownSetB q α β Λ) :
    (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  suffices H : ∀ n α β, α + β = n → ∀ Λ : Set (Partition × Partition), IsDownSetB q α β Λ →
      (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) from
    H _ α β rfl Λ hΛ
  intro n
  induction n with
  | zero =>
    intro α β h Λ _
    obtain ⟨rfl, rfl⟩ : α = 0 ∧ β = 0 := by omega
    exact card_ZLam_le_base F hΩ Λ
  | succ n ih =>
    intro α β h Λ hΛ
    rcases Nat.eq_zero_or_pos α with rfl | hα
    · -- case `α = 0`: the swap (Lemma S)
      have hβ : 1 ≤ β := by omega
      have hsw := card_ZLam_le_of_peel F hq hodd hbin hΩ hβ (isDownSetB_swapSet hΛ)
        (fun Λ' hΛ' => ih _ _ (by omega) Λ' hΛ')
      rw [(lemmaS_ii Ω 0 β Λ).2.2, (lemmaS_iii F q hodd 0 β Λ).2] at hsw
      exact hsw
    · -- case `α ≥ 1`: peeling `x_1`
      exact card_ZLam_le_of_peel F hq hodd hbin hΩ hα hΛ
        (fun Λ' hΛ' => ih _ _ (by omega) Λ' hΛ')

/-- **Theorem C** of `q_bip_induction.md` (the bipartite count): for a field `F` and `q ≥ 3` odd
with `C(q−1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`, and every `a ≥ 0`:
`dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`
(dimensions of the ideals as `F`-subspaces). -/
theorem theoremC (hq : 3 ≤ q) (hodd : Odd q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) (a : ℕ) :
    Nbal a q ≤ Module.finrank F ((Ibal F q a).restrictScalars F) ∧
      Nph a q ≤ Module.finrank F ((Iph F q a).restrictScalars F) ∧
      Nph a q = Nbal (a + 1) q := by
  have hΩ : Fintype.card (Fin q) = q := Fintype.card_fin q
  obtain ⟨hD1, hV1, hZ1⟩ := lemma72_i F hΩ a
  obtain ⟨hD2, hV2, hZ2⟩ := lemma72_ii F (by omega) hΩ a
  refine ⟨?_, ?_, lemma72_iii a q⟩
  · rw [← hV1, ← hZ1]
    exact thm76 F hq hodd hbin hΩ a a _ hD1
  · rw [← hV2, ← hZ2]
    exact thm76 F hq hodd hbin hΩ (a + 1) a _ hD2

end Bip

end
