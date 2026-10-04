module

public import RequestProject.OddPatterns.Defs

/-!
# Lemma B of `q_oddbox_patterns.md`

(B3) sizes, (B4) membership, (B5) monotonicity, (B6) the two examples.
-/

@[expose] public section

namespace OddPatterns

open ChainLemma OddShapes

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- Auxiliary for (B3) of `q_oddbox_patterns.md`: a family of pairwise disjoint finite sets
indexed by a finset has as union of cardinality the sum of the cardinalities. -/
theorem card_sup_of_disjoint {ι α : Type*} [DecidableEq α] (s : Finset ι) (g : ι → Finset α)
    (hg : (s : Set ι).PairwiseDisjoint g) : (s.sup g).card = ∑ i ∈ s, (g i).card := by
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion hg]

/-- Auxiliary for (B3) of `q_oddbox_patterns.md`: `λ'_1 = ℓ(λ)`. -/
theorem colLen_one (lam : Partition) : Tight.colLen lam 1 = lam.len := by
  unfold Tight.colLen Partition.len
  rw [List.filter_eq_self.2]
  intro x hx
  simpa using lam.pos x hx

/-- Auxiliary for (B3) of `q_oddbox_patterns.md`:
`Σ_{c=2}^{λ_1} λ'_c + ℓ(λ) = |λ|`. -/
theorem sum_colLen_two (lam : Partition) :
    ∑ c ∈ Finset.Icc 2 (lam.row 1), Tight.colLen lam c + lam.len = lam.size := by
  rcases Nat.eq_zero_or_pos (lam.row 1) with h0 | hpos
  · rw [h0, show Finset.Icc 2 0 = ∅ by rfl, Finset.sum_empty, zero_add]
    obtain ⟨parts, sorted, pos⟩ := lam
    cases parts with
    | nil => rfl
    | cons a l =>
      simp only [Partition.row] at h0
      exact absurd (pos a (by simp)) (by simp_all)
  · have hI : Finset.Icc 1 (lam.row 1) = insert 1 (Finset.Icc 2 (lam.row 1)) := by
      ext c; simp; omega
    have := Tight.sum_colLen lam
    rw [hI, Finset.sum_insert (by simp), colLen_one] at this
    omega

/-- **Lemma B, (B3)** of `q_oddbox_patterns.md` (sizes): for a marked pattern `T` of `λ` on `I`
with `|B_0| = ℓ + 1 + 2t`, `|I| = 2|P| + 2t + |λ| + 1`. -/
theorem B3 {m : ℕ} {lam : Partition} {I : Finset (Fin m)} (T : MarkedPattern lam I) (t : ℕ)
    (ht : T.marked.card = lam.len + 1 + 2 * t) :
    I.card = 2 * T.pairs.card + 2 * t + lam.size + 1 := by
  have hP : (T.pairs.sup id).card = 2 * T.pairs.card := by
    rw [card_sup_of_disjoint _ _ T.pairs_disjoint]
    simp only [id]
    rw [Finset.sum_congr rfl (fun e he => T.card_pair e he), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hB : ((Finset.Icc 2 (lam.row 1)).sup T.blocks).card =
      ∑ c ∈ Finset.Icc 2 (lam.row 1), Tight.colLen lam c := by
    rw [card_sup_of_disjoint _ _ T.blocks_disjoint]
    exact Finset.sum_congr rfl T.card_block
  have d1 : Disjoint (T.pairs.sup id) ((Finset.Icc 2 (lam.row 1)).sup T.blocks) := by
    rw [Finset.disjoint_sup_left]
    intro e he
    rw [Finset.disjoint_sup_right]
    exact fun c hc => T.pairs_blocks_disjoint e he c hc
  have d2 : Disjoint (T.pairs.sup id ∪ (Finset.Icc 2 (lam.row 1)).sup T.blocks) T.marked := by
    rw [Finset.disjoint_union_left, Finset.disjoint_sup_left, Finset.disjoint_sup_left]
    exact ⟨fun e he => T.pairs_marked_disjoint e he, fun c hc => T.blocks_marked_disjoint c hc⟩
  have hc := congrArg Finset.card T.cover
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, hP, hB, ht] at hc
  have := sum_colLen_two lam
  omega

/-- **Lemma B, (B4)** of `q_oddbox_patterns.md` (membership), first part: if `(λ, 0) ∈ Λ` and
`T` is a tight pattern of `λ` on `I`, then `T.prod ∈ V_Λ(I)`. -/
theorem B4_tight {m : ℕ} {Lam : Set Shape} {lam : Partition} (hlam : (lam, false) ∈ Lam)
    {I : Finset (Fin m)} (T : Tight.TightPattern lam I) :
    T.prod F (2 * h + 2) ∈ VS F h Lam I :=
  Ideal.mem_sup_left (Ideal.subset_span ⟨lam, hlam, T, rfl⟩)

/-- **Lemma B, (B4)** of `q_oddbox_patterns.md` (membership), second part: if `(λ, 1) ∈ Λ` and
`T` is a marked pattern of `λ` on `I`, then `T.prod ∈ V_Λ(I)`. -/
theorem B4_marked {m : ℕ} {Lam : Set Shape} {lam : Partition} (hlam : (lam, true) ∈ Lam)
    {I : Finset (Fin m)} (T : MarkedPattern lam I) :
    T.prod F h ∈ VS F h Lam I :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨lam, hlam, T, rfl⟩)

/-- **Lemma B, (B5)** of `q_oddbox_patterns.md` (monotone): if `Λ ⊆ Λ'` then
`V_Λ(I) ⊆ V_{Λ'}(I)`. -/
theorem B5_mono {m : ℕ} {Lam Lam' : Set Shape} (hsub : Lam ⊆ Lam') (I : Finset (Fin m)) :
    VS F h Lam I ≤ VS F h Lam' I := by
  unfold VS Tight.VLam
  refine sup_le_sup (Ideal.span_mono ?_) (Ideal.span_mono ?_)
  · rintro g ⟨lam, hlam, T, rfl⟩
    exact ⟨lam, hsub hlam, T, rfl⟩
  · rintro g ⟨lam, hlam, T, rfl⟩
    exact ⟨lam, hsub hlam, T, rfl⟩

/-- **Lemma B, (B5)** of `q_oddbox_patterns.md`: `V_∅(I) = 0`. -/
theorem B5_empty {m : ℕ} (I : Finset (Fin m)) : VS F h (∅ : Set Shape) I = ⊥ := by
  unfold VS Tight.VLam
  have e1 : {g | ∃ lam ∈ comp (∅ : Set Shape) false, ∃ T : Tight.TightPattern lam I,
      T.prod F (2 * h + 2) = g} = ∅ := by
    ext g; simp [comp]
  have e2 : {g | ∃ lam ∈ comp (∅ : Set Shape) true, ∃ T : MarkedPattern lam I,
      T.prod F h = g} = ∅ := by
    ext g; simp [comp]
  rw [e1, e2, Ideal.span_empty, bot_sup_eq]

/-- **Lemma B, (B5)** of `q_oddbox_patterns.md`: if `Λ` has no marked shape
(`comp Λ true = ∅`), then `V_Λ(I) = Tight.VLam F (2h+2) (comp Λ false) I`. -/
theorem B5_no_marked {m : ℕ} {Lam : Set Shape} (hLam : comp Lam true = ∅) (I : Finset (Fin m)) :
    VS F h Lam I = Tight.VLam F (2 * h + 2) (comp Lam false) I := by
  unfold VS
  have e2 : {g | ∃ lam ∈ comp Lam true, ∃ T : MarkedPattern lam I, T.prod F h = g} = ∅ := by
    ext g; simp [hLam]
  rw [e2, Ideal.span_empty, sup_bot_eq]

end OddPatterns
