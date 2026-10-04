module

public import RequestProject.BipP2.Main

/-!
# Items 3 and 4 of the Proofs of `q_any_bip.md`: Lemma 7.3 and Proposition 7.4 for every `q ≥ 2`

`q_any_bip.md`, **Proofs, "What the earlier proofs use"**:

* **item 3** (*Lemma 7.3, options, fibres, chain*): the parts of Lemma 7.3 of `q_bip_options.md`
  stated there with `q ≥ 3` (`Bip.lemma73_i`, `Bip.lemma73_ii`, `Bip.lemma73_ii_fiber`,
  `Bip.lemma73_ii_Zgt`, `Bip.lemma73_iv`, `Bip.lemma73_v`) hold for every `q ≥ 2`;
* **item 4** (*Proposition 7.4, the nine cases*): Proposition 7.4 of `q_bip_P2.md`
  (`Bip.prop74_i`, `Bip.prop74_ii_FLamB_le`, `Bip.prop74_ii_layer`, `Bip.prop74_ii`) holds for every
  `q ≥ 2`.

The proofs are those of `RequestProject/BipOpt/Main.lean` and `RequestProject/BipP2/Main.lean`,
which never use the bound on `q`.  The statements keep the hypothesis `2 ≤ q` asked for; as the
proofs show, it is not used (the statements hold for every `q`).
-/

@[expose] public section

namespace BipAny

open Bip ChainLemma ChainLemma.Partition

/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (i) of `q_bip_options.md` for every `q ≥ 2`):
for `α ≥ 1` and `μ ∈ BPar_q(α − 1, β)`, `opt_p(μ) ∈ BPar_q(α, β)` for every `p ∈ {1, …, q}`.
(The hypothesis `q ≥ 2` is not used.) -/
theorem lemma73_i {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) : ∀ p ∈ Finset.Icc 1 q, bopt q μ p ∈ BPar q α β :=
  fun _ hp => bopt_mem_BPar hα hμ (Finset.mem_Icc.1 hp).1 (Finset.mem_Icc.1 hp).2

/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (ii) of `q_bip_options.md`, main statement, for
every `q ≥ 2`): for `|Ω| = q`, `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)` and every tail `M'` of shape `μ`,
the multiset `{λ(u, M') : u ∈ Ω}` equals `{opt_p(μ) : p = 1, …, q}`.  (The hypotheses `q ≥ 2` and
`μ ∈ BPar_q(α − 1, β)` are not used.) -/
theorem lemma73_ii {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 2 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    (hM' : shape M'.1 M'.2 = μ) :
    Finset.univ.val.map (fun u => shape (consPt hα u M').1 (consPt hα u M').2) =
      (Finset.Icc 1 q).val.map (bopt q μ) :=
  map_shape_consPt hα hΩ M' hM'

/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (ii) of `q_bip_options.md`, first consequence,
for every `q ≥ 2`): for every down-set `Λ` of `BPar_q(α, β)` and every tail `M'` with shape `μ`,
`|F(M')| = F_Λ(μ)`.  (The hypotheses `q ≥ 2`, `μ ∈ BPar_q(α − 1, β)` and "`Λ` is a down-set" are
not used.) -/
theorem lemma73_ii_fiber {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 2 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) (hM' : shape M'.1 M'.2 = μ) :
    (Peel.fiber ((ZLam Ω α β Λ).map toTuple) (tailToTuple M')).card = FLamB q Λ μ :=
  card_fiber_eq_FLamB hα hΩ Λ M' hM'

/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (ii) of `q_bip_options.md`, second consequence,
for every `q ≥ 2`): for every down-set `Λ` of `BPar_q(α, β)` and every `i`, `Z_{>i} = Z_{Λ_i}`
(read through the tuples of the tails).  (The hypotheses `q ≥ 2` and "`Λ` is a down-set" are not
used.) -/
theorem lemma73_ii_Zgt {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 2 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {Λ : Set (Partition × Partition)}
    (hΛ : IsDownSetB q α β Λ) (i : ℕ) :
    Peel.Zgt ((ZLam Ω α β Λ).map toTuple) i =
      (ZLam Ω (α - 1) β (LamLayer q α β Λ i)).image tailToTuple :=
  Zgt_eq_ZLam_layer hα hΩ Λ i

open Classical in
/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (iv) of `q_bip_options.md` for every `q ≥ 2`):
for `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)` and every down-set `Λ` of `BPar_q(α, β)`,
`{p ∈ {1, …, q} : opt_p(μ) ∈ Λ} = {1, …, F_Λ(μ)}`.  (The hypothesis `q ≥ 2` is not used.) -/
theorem lemma73_iv {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) :
    (Finset.Icc 1 q).filter (fun p => bopt q μ p ∈ Λ) = Finset.Icc 1 (FLamB q Λ μ) :=
  bopt_mem_initial_segment hα hμ hΛ

/-- `q_any_bip.md`, **Proofs, item 3** (Lemma 7.3 (v) of `q_bip_options.md`, the three cases, for
every `q ≥ 2`): for `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)`, a down-set `Λ` of `BPar_q(α, β)` and
`Φ := F_Λ(μ) ≥ 1`, exactly one of the cases (α) `CaseAlpha`, (β) `CaseBeta`, (γ) `CaseGamma`
holds.  (The hypothesis `q ≥ 2` is not used.) -/
theorem lemma73_v {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (hΦ : 1 ≤ FLamB q Λ μ) :
    (CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        CaseGamma q Λ μ (FLamB q Λ μ)) :=
  three_cases hα hμ hΛ hΦ

/-- `q_any_bip.md`, **Proofs, item 4** (Proposition 7.4 (i) of `q_bip_P2.md` for every `q ≥ 2`):
for `α ≥ 1`, if `μ, μ̃ ∈ BPar_q(α − 1, β)` and `μ ≼ μ̃`, then `opt_p(μ) ≼ opt_p(μ̃)` for every
`p ∈ {1, …, q}` (`μ̃` is `ν`).  The proof is the nine-case analysis of `Bip.prop74_i`; the
hypotheses `q ≥ 2` and `α ≥ 1` are not used. -/
theorem prop74_i {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α) {μ ν : Partition × Partition}
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
    · rw [if_pos b1]; exact p2_case_RR hle hp1 a1 b1
    · rw [if_neg b1]
      split_ifs with b2
      · exact p2_case_RM hle hp1 a1
      · exact p2_case_RA hle hp1 a1 (by omega) (by omega)
  · rw [if_neg a1]
    by_cases a2 : p ≤ q - μ.1.len
    · rw [if_pos a2]
      by_cases b1 : p ≤ ν.2.len
      · rw [if_pos b1]; exact p2_case_MR hμ hν hle (by omega) b1
      · rw [if_neg b1]
        split_ifs with b2
        · exact p2_case_MM hle
        · exact p2_case_MA hle (by omega) (by omega)
    · rw [if_neg a2]
      by_cases b1 : p ≤ ν.2.len
      · rw [if_pos b1]; exact p2_case_AR hμ hν hle hpq (by omega) b1
      · rw [if_neg b1]
        split_ifs with b2
        · exact p2_case_AM hle (by omega) (by omega)
        · exact p2_case_AA hle (by omega) (by omega) (by omega)

/-- `q_any_bip.md`, **Proofs, item 4** (Proposition 7.4 (ii) of `q_bip_P2.md`, first statement,
for every `q ≥ 2`): for `α ≥ 1`, every down-set `Λ` of `BPar_q(α, β)` and
`μ ≼ μ̃` in `BPar_q(α − 1, β)`, `F_Λ(μ) ≥ F_Λ(μ̃)`. -/
theorem prop74_ii_FLamB_le {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) {μ ν : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) (hν : ν ∈ BPar q (α - 1) β) (hle : BWeakDom μ ν) :
    FLamB q Λ ν ≤ FLamB q Λ μ := by
  classical
  unfold FLamB
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hΛ.2 _ _ (BipAny.lemma73_i hq hα hμ p hp.1)
    (BipAny.prop74_i hq hα hμ hν hle p hp.1) hp.2⟩

/-- `q_any_bip.md`, **Proofs, item 4** (Proposition 7.4 (ii) of `q_bip_P2.md`, second statement,
for every `q ≥ 2`): for `α ≥ 1`, every down-set `Λ` of `BPar_q(α, β)` and every `i`, the layer
`Λ_i = {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` is a down-set of `BPar_q(α − 1, β)`. -/
theorem prop74_ii_layer {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) (i : ℕ) :
    IsDownSetB q (α - 1) β (LamLayer q α β Λ i) :=
  ⟨fun _ h => h.1, fun _ _ hlam hle hμ =>
    ⟨hlam, lt_of_lt_of_le hμ.2 (BipAny.prop74_ii_FLamB_le hq hα hΛ hlam hμ.1 hle)⟩⟩

/-- `q_any_bip.md`, **Proofs, item 4** (Proposition 7.4 (ii) of `q_bip_P2.md`, both statements, for
every `q ≥ 2`): `F_Λ` is antitone on `BPar_q(α − 1, β)` and every layer `Λ_i` is a down-set of
`BPar_q(α − 1, β)`. -/
theorem prop74_ii {q α β : ℕ} (hq : 2 ≤ q) (hα : 1 ≤ α) {Λ : Set (Partition × Partition)}
    (hΛ : IsDownSetB q α β Λ) :
    (∀ μ ν : Partition × Partition, μ ∈ BPar q (α - 1) β → ν ∈ BPar q (α - 1) β →
        BWeakDom μ ν → FLamB q Λ ν ≤ FLamB q Λ μ) ∧
      ∀ i, IsDownSetB q (α - 1) β (LamLayer q α β Λ i) :=
  ⟨fun _ _ hμ hν hle => BipAny.prop74_ii_FLamB_le hq hα hΛ hμ hν hle,
    BipAny.prop74_ii_layer hq hα hΛ⟩

end BipAny

end
