module

public import RequestProject.BipOpt.Defs

/-!
# Lemma 7.3 (i), (iii), (iv), (v) of `q_bip_options.md`

The purely combinatorial parts of **Lemma 7.3** of `q_bip_options.md`: the options stay in
`BPar_q(α, β)` (i), they form a chain (iii), the options in a down-set form an initial segment
(iv), and the three cases (α), (β), (γ) (v).
-/

@[expose] public section

namespace Bip

open ChainLemma ChainLemma.Partition

/-- The product order is reflexive (proof of **Lemma 7.3 (iii)** of `q_bip_options.md`). -/
theorem BWeakDom.refl (μ : Partition × Partition) : BWeakDom μ μ :=
  ⟨WeakDom.refl _, WeakDom.refl _⟩

/-- The product order is transitive (proof of **Lemma 7.3 (iii), (iv)** of
`q_bip_options.md`). -/
theorem BWeakDom.trans {a b c : Partition × Partition} (h1 : BWeakDom a b) (h2 : BWeakDom b c) :
    BWeakDom a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- **Lemma 7.3 (i)** of `q_bip_options.md`: for `α ≥ 1` and `μ ∈ BPar_q(α − 1, β)`,
`opt_p(μ) ∈ BPar_q(α, β)` for every `p ∈ {1, …, q}`.  (The Setting's hypothesis `q ≥ 3` and the
set `Ω` play no role here.) -/
theorem bopt_mem_BPar {q α β : ℕ} (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {p : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    bopt q μ p ∈ BPar q α β := by
  obtain ⟨h1, h2, h3⟩ := hμ
  unfold bopt
  split_ifs with ha hb
  · have := Lifts.size_subE μ.2 hp ha
    have := Lifts.len_subE_le μ.2 p
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [Lifts.size_addOne, Lifts.len_addOne]
    · push_cast at h1 ⊢; omega
    · omega
    · omega
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Lifts.size_addE μ.1 (show 1 ≤ q + 1 - p by omega)
        (show q + 1 - p ≤ μ.1.len by omega), Lifts.len_addE]
    · push_cast at h1 ⊢; omega
    · omega
    · omega

/-- **Lemma 7.3 (iii)** of `q_bip_options.md`, one step: if `ℓ_+ + ℓ_− ≤ q`, then
`opt_p(μ) ≼ opt_{p+1}(μ)` for every `1 ≤ p < q` (product order).  This only uses
`ℓ_+ + ℓ_− ≤ q`, as stated in the file. -/
theorem bopt_le_bopt_succ {q : ℕ} (μ : Partition × Partition) (hl : μ.1.len + μ.2.len ≤ q)
    {p : ℕ} (hp : 1 ≤ p) (hpq : p < q) : BWeakDom (bopt q μ p) (bopt q μ (p + 1)) := by
  unfold bopt
  have e1 : q + 1 - (p + 1) = q - p := by omega
  rw [e1]
  by_cases h1 : p + 1 ≤ μ.2.len
  · rw [if_pos (by omega), if_pos h1]
    exact ⟨WeakDom.refl _, μ.2.subE_mono p hp h1⟩
  by_cases h2 : p ≤ μ.2.len
  · rw [if_pos h2, if_neg h1]
    split_ifs with h3
    · exact ⟨μ.1.self_le_addOne, μ.2.subE_le_self p hp h2⟩
    · exact ⟨μ.1.self_le_addE _ (by omega) (by omega), μ.2.subE_le_self p hp h2⟩
  rw [if_neg h2, if_neg h1]
  by_cases h3 : p + 1 ≤ q - μ.1.len
  · rw [if_pos (by omega), if_pos h3]
    exact BWeakDom.refl _
  rw [if_neg h3]
  by_cases h4 : p ≤ q - μ.1.len
  · rw [if_pos h4]
    exact ⟨μ.1.addOne_le_addE _ (by omega) (by omega), WeakDom.refl _⟩
  · rw [if_neg h4]
    have e2 : q + 1 - p = (q - p) + 1 := by omega
    rw [e2]
    exact ⟨μ.1.addE_mono _ (by omega) (by omega), WeakDom.refl _⟩

/-- **Lemma 7.3 (iii)** of `q_bip_options.md`, chain form: if `ℓ_+ + ℓ_− ≤ q`, then
`opt_1(μ) ≼ opt_2(μ) ≼ ⋯ ≼ opt_q(μ)`, i.e. `opt_p(μ) ≼ opt_{p'}(μ)` whenever
`1 ≤ p ≤ p' ≤ q` (by transitivity of the product order).  This only uses `ℓ_+ + ℓ_− ≤ q`. -/
theorem bopt_mono {q : ℕ} (μ : Partition × Partition) (hl : μ.1.len + μ.2.len ≤ q)
    {p p' : ℕ} (hp : 1 ≤ p) (hpp' : p ≤ p') (hp'q : p' ≤ q) :
    BWeakDom (bopt q μ p) (bopt q μ p') := by
  induction p', hpp' using Nat.le_induction with
  | base => exact BWeakDom.refl _
  | succ n hn ih =>
    exact (ih (by omega)).trans (bopt_le_bopt_succ μ hl (by omega) (by omega))

open Classical in
/-- **Lemma 7.3 (iv)** of `q_bip_options.md`: for `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)` and every
down-set `Λ` of `BPar_q(α, β)`, `{p ∈ {1, …, q} : opt_p(μ) ∈ Λ} = {1, …, F_Λ(μ)}`.  (The Setting's
hypothesis `q ≥ 3` and the set `Ω` play no role here.) -/
theorem bopt_mem_initial_segment {q α β : ℕ} (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) :
    (Finset.Icc 1 q).filter (fun p => bopt q μ p ∈ Λ) = Finset.Icc 1 (FLamB q Λ μ) := by
  set A := (Finset.Icc 1 q).filter (fun p => bopt q μ p ∈ Λ) with hA
  have hl : μ.1.len + μ.2.len ≤ q := hμ.2.2
  have hdown : ∀ p ∈ A, ∀ p', 1 ≤ p' → p' ≤ p → p' ∈ A := by
    intro p hp p' hp' hp'p
    simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp', by omega⟩, hΛ.2 _ _ (bopt_mem_BPar hα hμ hp' (by omega))
      (bopt_mono μ hl hp' hp'p hp.1.2) hp.2⟩
  have hsub : A ⊆ Finset.Icc 1 q := Finset.filter_subset _ _
  have hAeq : A = Finset.Icc 1 (A.sup id) := by
    ext p
    simp only [Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨(Finset.mem_Icc.1 (hsub hp)).1, Finset.le_sup (f := id) hp⟩
    · rintro ⟨hp1, hp2⟩
      rcases A.eq_empty_or_nonempty with hAe | hAne
      · simp [hAe] at hp2; omega
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup A hAne id
        exact hdown m hm p hp1 (by simpa [hmax] using hp2)
  have hF : FLamB q Λ μ = A.card := by rw [FLamB, hA]
  rw [hF]
  conv_rhs => rw [hAeq]
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact hAeq

/-- Membership form of **Lemma 7.3 (iv)** of `q_bip_options.md`: for `1 ≤ p ≤ q`,
`opt_p(μ) ∈ Λ ↔ p ≤ F_Λ(μ)`. -/
theorem bopt_mem_iff {q α β : ℕ} (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    {p : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) : bopt q μ p ∈ Λ ↔ p ≤ FLamB q Λ μ := by
  classical
  have key := bopt_mem_initial_segment hα hμ hΛ
  have h1 : p ∈ (Finset.Icc 1 q).filter (fun p => bopt q μ p ∈ Λ) ↔ bopt q μ p ∈ Λ := by
    simp [Finset.mem_filter, hp, hpq]
  rw [← h1, key, Finset.mem_Icc]
  simp [hp]

/-- `F_Λ(μ) ≤ q` (proof of **Lemma 7.3 (v)** of `q_bip_options.md`). -/
theorem FLamB_le (q : ℕ) (Λ : Set (Partition × Partition)) (μ : Partition × Partition) :
    FLamB q Λ μ ≤ q := by
  classical
  unfold FLamB
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- **Lemma 7.3 (v), case (α)** of `q_bip_options.md`, as a proposition: `Φ > q − ℓ_+`, and with
`j_0 := q + 1 − Φ ∈ {1, …, ℓ_+}`: `(μ_+ + e_{j_0}, μ_−) = opt_Φ(μ) ∈ Λ`, and `j_0` is the first
row of its length: `j_0 = 1` or `μ_{+, j_0 − 1} > μ_{+, j_0}`. -/
def CaseAlpha (q : ℕ) (Λ : Set (Partition × Partition)) (μ : Partition × Partition) (Φ : ℕ) :
    Prop :=
  q - μ.1.len < Φ ∧ 1 ≤ q + 1 - Φ ∧ q + 1 - Φ ≤ μ.1.len ∧
    (μ.1.addE (q + 1 - Φ), μ.2) = bopt q μ Φ ∧ bopt q μ Φ ∈ Λ ∧
    (q + 1 - Φ = 1 ∨ μ.1.row (q + 1 - Φ) < μ.1.row (q + 1 - Φ - 1))

/-- **Lemma 7.3 (v), case (β)** of `q_bip_options.md`, as a proposition: `ℓ_− < Φ ≤ q − ℓ_+`,
and then `Φ = q − ℓ_+` (in particular `ℓ_+ + ℓ_− < q`) and `(μ_+ ⊔ 1, μ_−) = opt_Φ(μ) ∈ Λ`. -/
def CaseBeta (q : ℕ) (Λ : Set (Partition × Partition)) (μ : Partition × Partition) (Φ : ℕ) :
    Prop :=
  μ.2.len < Φ ∧ Φ ≤ q - μ.1.len ∧
    (Φ = q - μ.1.len ∧ μ.1.len + μ.2.len < q ∧
      (μ.1.addOne, μ.2) = bopt q μ Φ ∧ bopt q μ Φ ∈ Λ)

/-- **Lemma 7.3 (v), case (γ)** of `q_bip_options.md`, as a proposition: `1 ≤ Φ ≤ ℓ_−`, and with
`r := Φ`: `(μ_+, μ_− − e_r) = opt_r(μ) ∈ Λ`, and `r` is the last row of its length: `r = ℓ_−` or
`μ_{−, r+1} < μ_{−, r}`. -/
def CaseGamma (q : ℕ) (Λ : Set (Partition × Partition)) (μ : Partition × Partition) (Φ : ℕ) :
    Prop :=
  1 ≤ Φ ∧ Φ ≤ μ.2.len ∧
    (μ.1, μ.2.subE Φ) = bopt q μ Φ ∧ bopt q μ Φ ∈ Λ ∧
    (Φ = μ.2.len ∨ μ.2.row (Φ + 1) < μ.2.row Φ)

/-- **Lemma 7.3 (v)** of `q_bip_options.md`: for `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)`, a down-set `Λ`
of `BPar_q(α, β)` and `Φ := F_Λ(μ) ≥ 1`, exactly one of the cases (α) (`CaseAlpha`), (β)
(`CaseBeta`), (γ) (`CaseGamma`) holds.  (The Setting's hypothesis `q ≥ 3` and the set `Ω` play
no role here.) -/
theorem three_cases {q α β : ℕ} (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (hΦ : 1 ≤ FLamB q Λ μ) :
    (CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        CaseGamma q Λ μ (FLamB q Λ μ)) := by
  set Φ := FLamB q Λ μ with hΦdef
  have hΦq : Φ ≤ q := FLamB_le q Λ μ
  have hl : μ.1.len + μ.2.len ≤ q := hμ.2.2
  have hin : ∀ p, 1 ≤ p → p ≤ q → (bopt q μ p ∈ Λ ↔ p ≤ Φ) :=
    fun p hp hpq => bopt_mem_iff hα hμ hΛ hp hpq
  have hoptΦ := (hin Φ hΦ hΦq).2 le_rfl
  by_cases hγ : Φ ≤ μ.2.len
  · -- case (γ)
    right; right
    refine ⟨fun h => by have := h.1; omega, fun h => by have := h.1; omega, ?_⟩
    have hopt : bopt q μ Φ = (μ.1, μ.2.subE Φ) := by unfold bopt; rw [if_pos hγ]
    refine ⟨hΦ, hγ, hopt.symm, hoptΦ, ?_⟩
    rcases Nat.lt_or_ge Φ μ.2.len with hlt | hge
    · right
      have hle := μ.2.row_anti Φ (Φ + 1) hΦ (by omega) hlt
      by_contra hne
      have heq : μ.2.row (Φ + 1) = μ.2.row Φ := by omega
      have hopt' : bopt q μ (Φ + 1) = (μ.1, μ.2.subE (Φ + 1)) := by
        unfold bopt; rw [if_pos (by omega)]
      have hmem : bopt q μ (Φ + 1) ∈ Λ := by
        refine hΛ.2 _ _ (bopt_mem_BPar hα hμ (by omega) (by omega)) ?_ hoptΦ
        rw [hopt', hopt]
        exact ⟨WeakDom.refl _, Lifts.subE_le_of_row_eq μ.2 (by omega) hlt hΦ hγ heq⟩
      have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
      omega
    · left; omega
  by_cases hβ : Φ ≤ q - μ.1.len
  · -- case (β)
    right; left
    refine ⟨fun h => by have := h.1; omega, ?_, fun h => by have := h.2.1; omega⟩
    have hopt : bopt q μ Φ = (μ.1.addOne, μ.2) := by unfold bopt; rw [if_neg hγ, if_pos hβ]
    have hΦeq : Φ = q - μ.1.len := by
      by_contra hne
      have hopt' : bopt q μ (Φ + 1) = (μ.1.addOne, μ.2) := by
        unfold bopt; rw [if_neg (by omega), if_pos (by omega)]
      have := (hin (Φ + 1) (by omega) (by omega)).1 (hopt' ▸ hopt ▸ hoptΦ)
      omega
    exact ⟨by omega, hβ, hΦeq, by omega, hopt.symm, hoptΦ⟩
  · -- case (α)
    left
    refine ⟨?_, fun h => by have := h.2.1; omega, fun h => by have := h.2.1; omega⟩
    set j0 := q + 1 - Φ with hj0
    have hj01 : 1 ≤ j0 := by omega
    have hj0l : j0 ≤ μ.1.len := by omega
    have hopt : bopt q μ Φ = (μ.1.addE j0, μ.2) := by unfold bopt; rw [if_neg hγ, if_neg hβ]
    refine ⟨by omega, hj01, hj0l, hopt.symm, hoptΦ, ?_⟩
    rcases Nat.lt_or_ge 1 j0 with h2 | h2
    · right
      have hle := μ.1.row_anti (j0 - 1) j0 (by omega) (by omega) hj0l
      by_contra hne
      rw [← hj0] at hne
      have heq : μ.1.row (j0 - 1) = μ.1.row j0 := by omega
      have hopt' : bopt q μ (Φ + 1) = (μ.1.addE (j0 - 1), μ.2) := by
        unfold bopt; rw [if_neg (by omega), if_neg (by omega)]
        congr 2
      have hmem : bopt q μ (Φ + 1) ∈ Λ := by
        refine hΛ.2 _ _ (bopt_mem_BPar hα hμ (by omega) (by omega)) ?_ hoptΦ
        rw [hopt', hopt]
        exact ⟨Lifts.addE_le_of_row_eq μ.1 (by omega) (by omega) hj01 hj0l heq, WeakDom.refl _⟩
      have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
      omega
    · left; omega

end Bip

end
