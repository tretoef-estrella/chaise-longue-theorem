module

public import RequestProject.OddEquality.PartC

/-!
# (C3) of `q_oddbox_equality.md`: the ideal of one matching

The two equalities of **(C3)** of `q_oddbox_equality.md`, for any field `F` and any finite
nonempty `T ⊆ F` with `−T = T` (`|T| = r = q − 1` for the second one): the ideal of
`V(I_P) ∩ T^n` is `I_P + (g(y_i))`, `g(y) = Π_{u∈T} (y − u)`, and its ideal of top forms is
`I_P + (y_i^r)`. (Only the inclusion `gr ⊆ I_P + (y_i^r)` is used in (C4); it is
`OddEquality.top_mem_IPS_sup`.)
-/

@[expose] public section

open MvPolynomial

namespace OddEquality

variable {F : Type*} [Field F] {n : ℕ}

/-- **(C1)**, **(C3)** of `q_oddbox_equality.md`: `g(y_i) = Π_{u∈T} (y_i − u)`. -/
noncomputable def gT (T : Finset F) (i : Fin n) : MvPolynomial (Fin n) F :=
  ∏ u ∈ T, (X i - C u)

/-- **(C3)** of `q_oddbox_equality.md`: the ideal `(g(y_1), …, g(y_n))`. -/
noncomputable def GT (T : Finset F) : Ideal (MvPolynomial (Fin n) F) :=
  Ideal.span (Set.range (gT (n := n) T))

/-- **(C3)** of `q_oddbox_equality.md`: the ideal of the polynomials vanishing on `V(I_P) ∩ T^n`
(the points with coordinates in `T` and `M_{P(i)} = −M_i`). -/
noncomputable def IVP (T : Finset F) (P : ColComp.PerfMatch (Fin n)) :
    Ideal (MvPolynomial (Fin n) F) :=
  ⨅ (M : Fin n → F) (_ : ∀ i, M i ∈ T) (_ : ∀ i, M (P.1 i) = -M i), RingHom.ker (eval M)

/-- **(C3)** of `q_oddbox_equality.md` (proof): membership in the ideal of `V(I_P) ∩ T^n`. -/
theorem mem_IVP {T : Finset F} {P : ColComp.PerfMatch (Fin n)} {f : MvPolynomial (Fin n) F} :
    f ∈ IVP T P ↔ ∀ M : Fin n → F, (∀ i, M i ∈ T) → (∀ i, M (P.1 i) = -M i) → eval M f = 0 := by
  simp [IVP, Submodule.mem_iInf, RingHom.mem_ker]

/-- **(C3)** of `q_oddbox_equality.md` (proof): if `f` vanishes on `V(I_P) ∩ T^n`, then `σ_P(f)`
vanishes on the grid `T^n`. -/
theorem sigmaP_vanish {T : Finset F} (hneg : ∀ u ∈ T, -u ∈ T) {P : ColComp.PerfMatch (Fin n)}
    {f : MvPolynomial (Fin n) F} (hf : f ∈ IVP T P) (x : Fin n → F) (hx : ∀ i, x i ∈ T) :
    eval x (sigmaP P f) = 0 := by
  rw [eval_sigmaP]
  refine mem_IVP.1 hf _ (fun i => ?_) (sigmaPt_pair P x)
  unfold sigmaPt
  split_ifs
  · exact hx i
  · exact hneg _ (hx _)

/-- **(C3)** of `q_oddbox_equality.md`, first claim: for `T` finite, nonempty, with `−T = T`, the
ideal of `V(I_P) ∩ T^n` in `F[y]` is `I_P + (g(y_i))`. (Proof: `f − σ_P(f) ∈ I_P`, and `σ_P(f)`
vanishes on the grid `T^n`, hence lies in `(g(y_i))` by the Combinatorial Nullstellensatz.) -/
theorem C3_ideal {T : Finset F} (hTne : T.Nonempty) (hneg : ∀ u ∈ T, -u ∈ T)
    (P : ColComp.PerfMatch (Fin n)) : IVP T P = IPS P ⊔ GT T := by
  apply le_antisymm
  · intro f hf
    obtain ⟨h, -, hh⟩ := combinatorial_nullstellensatz_exists_linearCombination (fun _ => T)
      (fun _ => hTne) (sigmaP P f) (fun x hx => sigmaP_vanish hneg hf x hx)
    have hg : sigmaP P f ∈ GT T := by
      rw [hh, Finsupp.linearCombination_apply, Finsupp.sum]
      exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have e : f = (f - sigmaP P f) + sigmaP P f := by ring
    rw [e]
    exact add_mem (Ideal.mem_sup_left (sub_sigmaP_mem P f)) (Ideal.mem_sup_right hg)
  · refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, mem_IVP]
      intro M _ hP
      simp [hP a]
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, mem_IVP]
      intro M hM _
      simp only [gT, map_prod, map_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero (hM i) (sub_self _)

/-- **(C1)** of `q_oddbox_equality.md` (the top form of `g`): `deg g(y_i) ≤ |T|` and the component
of degree `|T|` of `g(y_i)` is `y_i^{|T|}` (so the top form of `g(y_i)` is `y_i^r`). -/
theorem gT_degree (T : Finset F) (i : Fin n) :
    (gT T i).totalDegree ≤ T.card ∧ homogeneousComponent T.card (gT T i) = X i ^ T.card := by
  classical
  unfold gT
  induction T using Finset.induction_on with
  | empty => simp [homogeneousComponent_zero]
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hlin : (X i - C a : MvPolynomial (Fin n) F).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans ?_
      simp
    refine ⟨(totalDegree_mul _ _).trans (by omega), ?_⟩
    have hX : homogeneousComponent (s.card + 1) (X i * ∏ u ∈ s, (X i - C u)) =
        X i * homogeneousComponent s.card (∏ u ∈ s, (X i - C u) : MvPolynomial (Fin n) F) := by
      have := Degeneration.homogeneousComponent_monomial_mul (s.card + 1) (Finsupp.single i 1)
        (1 : F) (∏ u ∈ s, (X i - C u))
      rw [if_pos (by simp), show s.card + 1 - (Finsupp.single i 1).degree = s.card by simp] at this
      exact this
    rw [sub_mul, map_sub, homogeneousComponent_C_mul,
      homogeneousComponent_eq_zero (s.card + 1) (∏ u ∈ s, (X i - C u)) (by omega), mul_zero,
      sub_zero, hX, h2, pow_succ, mul_comm]

/-- **(C3)** of `q_oddbox_equality.md` (proof): `f ∈ I`, `deg f ≤ d` ⇒ `f_d ∈ gr(I)`. -/
theorem homogeneousComponent_mem_gr_of_le {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin n) F} (hf : f ∈ I) {d : ℕ} (hd : f.totalDegree ≤ d) :
    homogeneousComponent d f ∈ Degeneration.gr I := by
  have h := Degeneration.grPart_le_span I d (Degeneration.mem_grPart.2 ⟨f, hf, hd, rfl⟩)
  rwa [← Degeneration.gr_restrictScalars_eq_span, Submodule.restrictScalars_mem] at h

/-- **(C3)** of `q_oddbox_equality.md`, second claim: for `T` finite with `|T| = q − 1 ≥ 1` and
`−T = T`, the ideal of top forms of `I_P + (g(y_i))` is `I_P + (y_i^{q−1})`. -/
theorem C3_top (q : ℕ) (hq : 2 ≤ q) {T : Finset F} (hT : T.card = q - 1)
    (hneg : ∀ u ∈ T, -u ∈ T) (P : ColComp.PerfMatch (Fin n)) :
    Degeneration.gr (IPS P ⊔ GT T) = IPS P ⊔ Peel.powIdeal F q n := by
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  apply le_antisymm
  · rw [Degeneration.gr, Ideal.span_le]
    rintro _ ⟨f, hf, -, rfl⟩
    rw [← C3_ideal hTne hneg P] at hf
    exact top_mem_IPS_sup q T hT hneg P f (mem_IVP.1 hf)
  · refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      have hmem : (X a + X (P.1 a) : MvPolynomial (Fin n) F) ∈ IPS P ⊔ GT T :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨a, rfl⟩)
      have hhom : (X a + X (P.1 a) : MvPolynomial (Fin n) F).IsHomogeneous 1 :=
        (isHomogeneous_X F a).add (isHomogeneous_X F _)
      have h := homogeneousComponent_mem_gr_of_le hmem (hhom.totalDegree_le)
      rwa [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hhom), if_pos rfl] at h
    · rintro _ ⟨i, rfl⟩
      obtain ⟨h1, h2⟩ := gT_degree T i
      have h := homogeneousComponent_mem_gr_of_le
        (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩) : gT T i ∈ IPS P ⊔ GT T) h1
      rwa [h2, hT] at h

end OddEquality

end
