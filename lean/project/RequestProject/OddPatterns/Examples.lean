module

public import RequestProject.OddPatterns.LemmaB

/-!
# (B6) of `q_oddbox_patterns.md`: two examples

In `C_1`, `V_{{(∅, 1)}} = (y_1^{2h})`; in `C_2`, `V_{{((1), 1)}} = (D^−(y_1, y_2))`.
(The indices `1, 2` of the file are the elements `0, 1` of `Fin m`.)
-/

@[expose] public section

namespace OddPatterns

open ChainLemma OddShapes

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- Auxiliary for (B6) of `q_oddbox_patterns.md`: a set of shapes with no unmarked shape gives
the zero unmarked part. -/
theorem VLam_comp_false_singleton_true {m : ℕ} (lam0 : Partition) (I : Finset (Fin m)) :
    Tight.VLam F (2 * h + 2) (comp ({(lam0, true)} : Set Shape) false) I = ⊥ := by
  unfold Tight.VLam
  have : {g | ∃ lam ∈ comp ({(lam0, true)} : Set Shape) false,
      ∃ T : Tight.TightPattern lam I, T.prod F (2 * h + 2) = g} = ∅ := by
    ext g; simp [comp]
  rw [this, Ideal.span_empty]

/-- Auxiliary for (B6) of `q_oddbox_patterns.md`. -/
theorem comp_singleton_true (lam0 : Partition) :
    comp ({(lam0, true)} : Set Shape) true = {lam0} := by
  ext lam; simp [comp]

/-- **Lemma B, (B6)** of `q_oddbox_patterns.md`, first example: in `C_1`, every marked pattern
of the empty partition on `{1}` has the product `y_1^{2h}`. -/
theorem B6_empty_prod (T : MarkedPattern emptyPart (Finset.univ : Finset (Fin 1))) :
    T.prod F h = Tight.y F (2 * h + 2) 0 ^ (2 * h) := by
  have hP : T.pairs = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have := T.card_pair e he
    have := Finset.card_le_univ e
    simp at this; omega
  have hI : Finset.Icc 2 (emptyPart.row 1) = ∅ := rfl
  have hM : T.marked = Finset.univ := by
    apply Finset.eq_univ_of_card
    obtain ⟨t, ht⟩ := T.marked_card
    have := Finset.card_le_univ T.marked
    simp only [Fintype.card_fin] at this ⊢
    exact le_antisymm this (by omega)
  have hlen : emptyPart.len = 0 := rfl
  unfold MarkedPattern.prod
  rw [hP, hI, Finset.prod_empty, Finset.prod_empty, one_mul, mul_one, hlen]
  unfold markedPf
  have hc : 1 = T.marked.card := by rw [hM]; rfl
  rw [← mPf_cast h 0 hc, A1]
  congr 1
  exact congrArg _ (Subsingleton.elim _ _)

/-- **Lemma B, (B6)** of `q_oddbox_patterns.md`, first example: in `C_1`,
`V_{{(∅, 1)}} = (y_1^{2h})`. -/
theorem B6_empty :
    VSAll F h 1 ({(emptyPart, true)} : Set Shape) =
      Ideal.span {Tight.y F (2 * h + 2) 0 ^ (2 * h)} := by
  unfold VSAll VS
  rw [VLam_comp_false_singleton_true, bot_sup_eq, comp_singleton_true]
  congr 1
  ext g
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, rfl⟩
    exact B6_empty_prod T
  · rintro rfl
    refine ⟨MarkedPattern.mk ∅ (fun _ => ∅) Finset.univ (by simp) (by simp)
      (fun c hc => absurd hc (by simp [show emptyPart.row 1 = 0 from rfl]))
      (by simp [show emptyPart.row 1 = 0 from rfl]) (by simp) (by simp) (by simp) ⟨0, rfl⟩
      (by ext x; simp), B6_empty_prod _⟩

/-- **Lemma B, (B6)** of `q_oddbox_patterns.md`, second example: in `C_2`, every marked pattern
of the partition `(1)` on `{1, 2}` has the product `D^−(y_1, y_2)`. -/
theorem B6_one_prod (T : MarkedPattern onePart (Finset.univ : Finset (Fin 2))) :
    T.prod F h = ColOne.Dab (2 * h + 1) (Tight.y F (2 * h + 2) 0) (Tight.y F (2 * h + 2) 1) := by
  have hM : T.marked = Finset.univ := by
    apply Finset.eq_univ_of_card
    obtain ⟨t, ht⟩ := T.marked_card
    have := Finset.card_le_univ T.marked
    simp only [Fintype.card_fin] at this ⊢
    have hl : onePart.len = 1 := rfl
    omega
  have hP : T.pairs = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have h1 := T.card_pair e he
    have h2 := T.pairs_marked_disjoint e he
    rw [hM] at h2
    have he0 : e = ∅ := Finset.eq_empty_of_forall_notMem fun x hx =>
      Finset.disjoint_left.1 h2 hx (Finset.mem_univ x)
    rw [he0] at h1
    simp at h1
  have hI : Finset.Icc 2 (onePart.row 1) = ∅ := rfl
  have hlen : onePart.len = 1 := rfl
  unfold MarkedPattern.prod
  rw [hP, hI, Finset.prod_empty, Finset.prod_empty, one_mul, mul_one, hlen]
  unfold markedPf
  have hc : 2 = T.marked.card := by rw [hM]; rfl
  rw [← mPf_cast h 1 hc, A2]
  have hmono := (T.marked.orderEmbOfFin rfl).strictMono
    (show Fin.cast hc 0 < Fin.cast hc 1 by simp [Fin.lt_def])
  have e0 : T.marked.orderEmbOfFin rfl (Fin.cast hc 0) = 0 := by
    apply Fin.ext; have := (T.marked.orderEmbOfFin rfl (Fin.cast hc 1)).isLt
    rw [Fin.lt_def] at hmono; simp; omega
  have e1 : T.marked.orderEmbOfFin rfl (Fin.cast hc 1) = 1 := by
    apply Fin.ext; have := (T.marked.orderEmbOfFin rfl (Fin.cast hc 1)).isLt
    rw [Fin.lt_def] at hmono; simp; omega
  rw [e0, e1]

/-- **Lemma B, (B6)** of `q_oddbox_patterns.md`, second example: in `C_2`,
`V_{{((1), 1)}} = (D^−(y_1, y_2))`. -/
theorem B6_one :
    VSAll F h 2 ({(onePart, true)} : Set Shape) =
      Ideal.span {ColOne.Dab (2 * h + 1) (Tight.y F (2 * h + 2) 0) (Tight.y F (2 * h + 2) 1)} := by
  unfold VSAll VS
  rw [VLam_comp_false_singleton_true, bot_sup_eq, comp_singleton_true]
  congr 1
  ext g
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, rfl⟩
    exact B6_one_prod T
  · rintro rfl
    refine ⟨MarkedPattern.mk ∅ (fun _ => ∅) Finset.univ (by simp) (by simp)
      (fun c hc => absurd hc (by simp [show onePart.row 1 = 1 from rfl]))
      (by simp [show onePart.row 1 = 1 from rfl]) (by simp) (by simp) (by simp) ⟨0, rfl⟩
      (by ext x; simp), B6_one_prod _⟩

end OddPatterns
