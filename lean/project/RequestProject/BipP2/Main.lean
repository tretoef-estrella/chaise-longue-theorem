module

public import RequestProject.BipP2.Cases

/-!
# Proposition 7.4 of `q_bip_P2.md` (the layers are down-sets)

**Proposition 7.4 (i)** (options of pairs of partitions are monotone) and **(ii)** (`F_Λ` is
antitone and the layers `Λ_i` are down-sets) of `q_bip_P2.md`, reusing `Bip.bopt` (`opt_p`),
`Bip.FLamB` (`F_Λ`), `Bip.LamLayer` (`Λ_i`), `Bip.BPar`, `Bip.BWeakDom` (`≼`) and
`Bip.IsDownSetB` (down-sets of `BPar_q(α, β)`).  `μ̃` of the file is written `ν`.  The nine
cases of the proof are the lemmas `Bip.p2_case_RR`, …, `Bip.p2_case_AR` of
`RequestProject/BipP2/Cases.lean`.
-/

@[expose] public section

namespace Bip

open ChainLemma ChainLemma.Partition

/-- **Proposition 7.4 (i)** of `q_bip_P2.md`: for `q ≥ 3`, `α ≥ 1`, if
`μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then `opt_p(μ) ≼ opt_p(μ̃)` for every
`p ∈ {1, …, q}`.  (Here `μ̃` is `ν`.)

The proof is the case analysis of the file: each position `p` is a removal (R), a middle
position (M) or an addition (A) for `μ` and for `μ̃`, giving the nine cases RR, RM, RA, MR, MM,
MA, AR, AM, AA.  (The hypotheses `q ≥ 3` and `α ≥ 1` of the Setting are kept, but the proof does
not need them.) -/
theorem prop74_i {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) {μ ν : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β) (hle : BWeakDom μ ν) :
    ∀ p ∈ Finset.Icc 1 q, BWeakDom (bopt q μ p) (bopt q ν p) := by
  intro p hp
  obtain ⟨hp1, hpq⟩ := Finset.mem_Icc.1 hp
  have hlμ := hμ.2.2
  have hlν := hν.2.2
  unfold bopt
  by_cases a1 : p ≤ μ.2.len
  · rw [if_pos a1]
    by_cases b1 : p ≤ ν.2.len
    · -- case RR
      rw [if_pos b1]; exact p2_case_RR hle hp1 a1 b1
    · rw [if_neg b1]
      split_ifs with b2
      · -- case RM
        exact p2_case_RM hle hp1 a1
      · -- case RA
        exact p2_case_RA hle hp1 a1 (by omega) (by omega)
  · rw [if_neg a1]
    by_cases a2 : p ≤ q - μ.1.len
    · rw [if_pos a2]
      by_cases b1 : p ≤ ν.2.len
      · -- case MR
        rw [if_pos b1]; exact p2_case_MR hμ hν hle (by omega) b1
      · rw [if_neg b1]
        split_ifs with b2
        · -- case MM
          exact p2_case_MM hle
        · -- case MA
          exact p2_case_MA hle (by omega) (by omega)
    · rw [if_neg a2]
      by_cases b1 : p ≤ ν.2.len
      · -- case AR
        rw [if_pos b1]; exact p2_case_AR hμ hν hle hpq (by omega) b1
      · rw [if_neg b1]
        split_ifs with b2
        · -- case AM
          exact p2_case_AM hle (by omega) (by omega)
        · -- case AA
          exact p2_case_AA hle (by omega) (by omega) (by omega)

/-- **Proposition 7.4 (ii)** of `q_bip_P2.md`, first statement: for `q ≥ 3`, `α ≥ 1` and every
down-set `Λ` of `BPar_q(α, β)`, if `μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then
`F_Λ(μ) ≥ F_Λ(μ̃)`.  (Proof as in the file: `opt_p(μ̃) ∈ Λ` gives `opt_p(μ) ∈ Λ` by (i) and
Lemma 7.3 (i).) -/
theorem prop74_ii_FLamB_le {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) {μ ν : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β) (hle : BWeakDom μ ν) :
    FLamB q Λ ν ≤ FLamB q Λ μ := by
  classical
  unfold FLamB
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hΛ.2 _ _ (lemma73_i hq hα hμ p hp.1) (prop74_i hq hα hμ hν hle p hp.1) hp.2⟩

/-- **Proposition 7.4 (ii)** of `q_bip_P2.md`, second statement: for `q ≥ 3`, `α ≥ 1`, every
down-set `Λ` of `BPar_q(α, β)` and every `i`, the layer
`Λ_i = {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` is a down-set of `BPar_q(α − 1, β)`. -/
theorem prop74_ii_layer {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) (i : ℕ) :
    IsDownSetB q (α - 1) β (LamLayer q α β Λ i) :=
  ⟨fun _ h => h.1, fun _ _ hlam hle hμ =>
    ⟨hlam, lt_of_lt_of_le hμ.2 (prop74_ii_FLamB_le hq hα hΛ hlam hμ.1 hle)⟩⟩

/-- **Proposition 7.4 (ii)** of `q_bip_P2.md` (both statements together): for `q ≥ 3`, `α ≥ 1`
and every down-set `Λ` of `BPar_q(α, β)`: if `μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then
`F_Λ(μ) ≥ F_Λ(μ̃)`; and every layer `Λ_i = {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` is a down-set of
`BPar_q(α − 1, β)`. -/
theorem prop74_ii {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) {Λ : Set (Partition × Partition)}
    (hΛ : IsDownSetB q α β Λ) :
    (∀ μ ν : Partition × Partition, μ ∈ BPar q (α - 1) β → ν ∈ BPar q (α - 1) β →
        BWeakDom μ ν → FLamB q Λ ν ≤ FLamB q Λ μ) ∧
      ∀ i, IsDownSetB q (α - 1) β (LamLayer q α β Λ i) :=
  ⟨fun _ _ hμ hν hle => prop74_ii_FLamB_le hq hα hΛ hμ hν hle, prop74_ii_layer hq hα hΛ⟩

end Bip

end
