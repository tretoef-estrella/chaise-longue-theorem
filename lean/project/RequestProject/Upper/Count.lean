module

public import RequestProject.Upper.Defs

/-!
# Steps (i) and (ii) of `q3_upper_bound.md`: the support `Σ`

A point `z ∈ {1, −1}^{n'}` with `g_J(z) ≠ 0` has `k` or `k + 1` coordinates equal to `1`,
hence `|Σ| ≤ binomial(2k+1, k) + binomial(2k+1, k+1) = binomial(2k+2, k+1)`.
-/

@[expose] public section

open MvPolynomial Finset

namespace BallotBound

variable {F : Type*} [Field F] {k : ℕ}

/-- Step (ii) of `q3_upper_bound.md`: if `g_J(z) ≠ 0` for the point `z` attached to `A`, then
the number of coordinates of `z` equal to `1` is `k` or `k + 1`. -/
theorem card_eq_of_eval_g_ne_zero (A : Finset (Fin (2 * k + 1))) (J : Matching k)
    (h : eval (pt F k A) (g J) ≠ 0) : A.card = k ∨ A.card = k + 1 := by
  classical
  set z : Fin (2 * k + 2) → F := fun x => eval (pt F k A) (yP F k x) with hz
  have hne : ∀ a, a ≠ 0 → J.1 a ≠ 0 → a < J.1 a → z (J.1 a) ≠ z a := by
    intro a h1 h2 h3 h4
    apply h
    rw [g, map_prod]
    refine prod_eq_zero (i := a) (by simp [h1, h2, h3]) ?_
    rw [map_sub, sub_eq_zero]; exact h4
  let w : Fin (2 * k + 2) → ℤ := Fin.cases 0 (fun i => if i ∈ A then 1 else -1)
  have hzw : ∀ x y, x ≠ 0 → y ≠ 0 → z x ≠ z y → w y = - w x := by
    intro x y hx hy hxy
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hx
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hy
    simp only [hz, yP, Fin.cases_succ, eval_X, pt] at hxy
    simp only [w, Fin.cases_succ]
    split_ifs at hxy ⊢ <;> simp_all
  have hJ := J.2
  have hinv : Function.Involutive J.1 := fun x => (hJ x).2
  have hJ0 : J.1 0 ≠ 0 := (hJ 0).1
  set f : Fin (2 * k + 2) → ℤ := fun x => w x - if x = J.1 0 then w (J.1 0) else 0 with hf
  have hfJ : ∀ x, f (J.1 x) = - f x := by
    intro x
    by_cases hx0 : x = 0
    · subst hx0; simp [hf, w, Ne.symm hJ0]
    by_cases hx1 : x = J.1 0
    · subst hx1; simp [hf, w, hinv 0, Ne.symm hJ0]
    have hJx0 : J.1 x ≠ 0 := fun e => hx1 (by rw [← e, hinv x])
    have hJx1 : J.1 x ≠ J.1 0 := fun e => hx0 (hinv.injective e)
    simp only [hf, if_neg hx1, if_neg hJx1, sub_zero]
    rcases lt_or_gt_of_ne (hJ x).1 with hlt | hlt
    · have h1 := hne (J.1 x) hJx0 (by rw [hinv x]; exact hx0) (by rw [hinv x]; exact hlt)
      rw [hinv x] at h1
      exact hzw _ _ hx0 hJx0 h1
    · exact hzw _ _ hx0 hJx0 (hne x hx0 hJx0 hlt).symm
  have hsum0 : ∑ x, f x = 0 := by
    have := Equiv.sum_comp hinv.toPerm f
    simp only [Function.Involutive.coe_toPerm, hfJ, sum_neg_distrib] at this
    linarith
  have hsumw : ∑ x, w x = 2 * (A.card : ℤ) - (2 * k + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [w, Fin.cases_zero, Fin.cases_succ, zero_add]
    rw [sum_ite, sum_const, sum_const]
    simp only [filter_mem_eq_inter, univ_inter]
    have := card_compl A
    rw [Fintype.card_fin] at this
    rw [show (univ.filter fun x => x ∉ A) = Aᶜ by ext; simp, this]
    have hA : A.card ≤ 2 * k + 1 := by simpa using card_le_univ A
    simp only [nsmul_eq_mul, mul_one, mul_neg]
    rw [Nat.cast_sub hA]; push_cast; ring
  have hwJ0 : w (J.1 0) = 1 ∨ w (J.1 0) = -1 := by
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hJ0
    rw [← hi]; simp only [w, Fin.cases_succ]; split_ifs <;> simp
  have : ∑ x, f x = ∑ x, w x - w (J.1 0) := by
    simp [hf, sum_sub_distrib]
  omega

/-- Step (ii) of `q3_upper_bound.md`: `|Σ| ≤ binomial(2k+2, k+1)`. -/
theorem card_supp_le : (supp F k).card ≤ (2 * k + 2).choose (k + 1) := by
  classical
  have hsub : supp F k ⊆ powersetCard k univ ∪ powersetCard (k + 1) univ := by
    intro A hA
    rw [supp, mem_filter] at hA
    obtain ⟨J, hJ⟩ := hA.2
    rcases card_eq_of_eval_g_ne_zero A J hJ with h | h
    · exact mem_union_left _ (mem_powersetCard.2 ⟨subset_univ _, h⟩)
    · exact mem_union_right _ (mem_powersetCard.2 ⟨subset_univ _, h⟩)
  calc (supp F k).card ≤ (powersetCard k univ ∪ powersetCard (k + 1) univ).card :=
        card_le_card hsub
    _ ≤ (powersetCard k (univ : Finset (Fin (2 * k + 1)))).card +
        (powersetCard (k + 1) (univ : Finset (Fin (2 * k + 1)))).card := card_union_le _ _
    _ = (2 * k + 2).choose (k + 1) := by
        rw [card_powersetCard, card_powersetCard, card_univ, Fintype.card_fin]
        exact (Nat.choose_succ_succ (2 * k + 1) k).symm

end BallotBound

end
