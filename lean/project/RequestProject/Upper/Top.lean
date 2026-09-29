module

public import RequestProject.Upper.Defs

/-!
# Steps (iii) and (iv) of `q3_upper_bound.md`: functions on `{1, −1}^{n'}` and top-degree forms

The Chinese remainder theorem of step (iii) identifies `S/(y_i^2 − 1 : i)` with the ring of
functions on `T^{n'}`; in particular (this is the part we use) a polynomial vanishing on `T^{n'}`
lies in `(y_i^2 − 1 : i)`, with degree control.  We use the combinatorial Nullstellensatz of
Mathlib for this.  Step (iv) then says: if a form `p` of degree `d` agrees on `T^{n'}` with a
polynomial of degree `< d`, then `p ∈ (y_1^2, …, y_{n'}^2)`, i.e. the top-degree form of an
element of `(y_i^2 − 1 : i)` lies in `(y_i^2 : i)`.
-/

@[expose] public section

open MvPolynomial Finset

namespace BallotBound

variable {F : Type*} [Field F] {k : ℕ}

/-- Step (iii) of `q3_upper_bound.md` (the Chinese remainder theorem for `y^2 − 1 =
(y − 1)(y + 1)`, `1 ≠ −1`): a polynomial vanishing at all points of `T^{n'}` lies in the ideal
`(y_1^2 − 1, …, y_{n'}^2 − 1)`, as a combination `∑ h_i (y_i^2 − 1)` with
`deg (h_i (y_i^2 − 1)) ≤ deg f`. -/
theorem exists_sq_sub_one_combination (hF : ringChar F ≠ 2) (f : MvPolynomial (Fin (2 * k + 1)) F)
    (hf : ∀ A, eval (pt F k A) f = 0) :
    ∃ h : Fin (2 * k + 1) → MvPolynomial (Fin (2 * k + 1)) F,
      (∀ i, ((X i ^ 2 - 1) * h i).totalDegree ≤ f.totalDegree) ∧
      f = ∑ i, (X i ^ 2 - 1) * h i := by
  classical
  have h1 : (1 : F) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two hF).symm
  have hP : ∀ i : Fin (2 * k + 1), ∏ r ∈ ({1, -1} : Finset F), (X i - C r) =
      (X i ^ 2 - 1 : MvPolynomial (Fin (2 * k + 1)) F) := by
    intro i
    rw [prod_pair h1]; simp; ring
  obtain ⟨h, hdeg, hf'⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ => ({1, -1} : Finset F)) (fun _ => by simp) f (by
      intro x hx
      have : x = pt F k (univ.filter fun i => x i = 1) := by
        funext i
        simp only [pt, mem_filter, mem_univ, true_and]
        split_ifs with h
        · exact h
        · have := hx i; simp at this; tauto
      rw [this]; exact hf _)
  refine ⟨h, fun i => ?_, ?_⟩
  · simpa [hP] using hdeg i
  · rw [hf', Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [hP, mul_comm]

/-- Step (iv) of `q3_upper_bound.md` (top-degree forms): if a form `p` of degree `d` agrees on
`T^{n'}` with a polynomial `q` all of whose monomials have degree `< d`, then
`p ∈ (y_1^2, …, y_{n'}^2)`; indeed `p` is the top-degree form of `p − q ∈ (y_i^2 − 1 : i)`, and
the top-degree form of `y_i^2 − 1` is `y_i^2`. -/
theorem mem_squaresIdeal_of_eval_eq (hF : ringChar F ≠ 2) {d : ℕ}
    {p q : MvPolynomial (Fin (2 * k + 1)) F} (hp : p.IsHomogeneous d)
    (hq : ∀ m ∈ q.support, m.degree < d) (h : ∀ A, eval (pt F k A) p = eval (pt F k A) q) :
    p ∈ squaresIdeal F k := by
  classical
  obtain ⟨hh, hdeg, hf⟩ := exists_sq_sub_one_combination hF (p - q) (fun A => by
    rw [map_sub, h A, sub_self])
  have hfd : (p - q).totalDegree ≤ d := by
    refine (totalDegree_sub _ _).trans (max_le hp.totalDegree_le ?_)
    rw [totalDegree]
    refine Finset.sup_le fun m hm => ?_
    have := hq m hm
    rw [Finsupp.degree] at this
    exact this.le
  rw [mem_squaresIdeal_iff]
  intro m hm
  have hmd : m.degree = d := by
    have := hp (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have hqm : coeff m q = 0 := by
    by_contra hc
    have := hq m (mem_support_iff.mpr hc)
    omega
  have hfm : coeff m (p - q) ≠ 0 := by
    rw [coeff_sub, hqm, sub_zero]; exact mem_support_iff.mp hm
  rw [hf, coeff_sum] at hfm
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfm
  refine ⟨i, ?_⟩
  have hhi : coeff m (hh i) = 0 := by
    by_cases h0 : hh i = 0
    · simp [h0]
    have h2 : 2 ≤ (X i ^ 2 - 1 : MvPolynomial (Fin (2 * k + 1)) F).totalDegree := by
      have hm2 : Finsupp.single i 2 ∈ (X i ^ 2 - 1 : MvPolynomial (Fin (2 * k + 1)) F).support := by
        rw [mem_support_iff, coeff_sub, X_pow_eq_monomial, coeff_monomial, if_pos rfl, coeff_one,
          if_neg (Finsupp.single_ne_zero.mpr two_ne_zero).symm]
        simp
      have := le_totalDegree hm2
      simpa using this
    have h3 := hdeg i
    rw [totalDegree_mul_of_isDomain (by intro h; simp [h] at h2) h0] at h3
    apply coeff_eq_zero_of_totalDegree_lt
    have : m.degree = ∑ j ∈ m.support, m j := rfl
    omega
  rw [sub_mul, one_mul, coeff_sub, hhi, sub_zero, X_pow_eq_monomial, coeff_monomial_mul'] at hi
  split_ifs at hi with hle
  · simpa using hle i
  · exact absurd rfl hi

end BallotBound

end
