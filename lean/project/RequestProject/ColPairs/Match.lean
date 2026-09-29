module

public import Mathlib

/-!
# Bijections between the two sides of a pair block (`q_col_pairs.md`, proof of Lemma 6.7 (iii))

The combinatorial part of the **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`, stated for
abstract finite types `X` (standing for `A`) and `Y` (standing for `B`):
* `match_bal`: when both sides are enumerated by `[a]`, the bijections `σ : X → Y` are the maps
  `e_Y ∘ τ ∘ e_X^{−1}` with `τ` a permutation of `[a]`;
* `match_ph`: when `Y` has one extra element `y_0` (the vertex `0`), a bijection `σ : X → Y` is the
  same as an element `i_0` (the one sent to `y_0`) together with a bijection
  `[m+1] ∖ {i_0} → [m]`, and the product over the pairs avoiding `y_0` is the corresponding
  product.
-/

@[expose] public section

namespace ColPairs

variable {M : Type*} [CommMonoid M]

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`, case `0 ∉ A ∪ B`: the bijections `A → B`
are the maps `σ = e_B ∘ τ ∘ e_A^{−1}` with `τ` a permutation of `[a]`, and the product over the
pairs `{i, σ(i)}` is the product over the pairs `{e_A(i), e_B(τ(i))}`; every `τ` arises. -/
theorem match_bal {X Y : Type*} [Fintype X] [Fintype Y] {a : ℕ} (eX : Fin a ≃ X) (eY : Fin a ≃ Y)
    (f : X → Y → M) :
    (∀ σ : X ≃ Y, ∃ τ : Equiv.Perm (Fin a), ∏ x, f x (σ x) = ∏ i, f (eX i) (eY (τ i))) ∧
    (∀ τ : Equiv.Perm (Fin a), ∃ σ : X ≃ Y, ∏ x, f x (σ x) = ∏ i, f (eX i) (eY (τ i))) := by
  constructor
  · intro σ
    refine ⟨(eX.trans σ).trans eY.symm, ?_⟩
    rw [← Equiv.prod_comp eX]
    simp
  · intro τ
    refine ⟨(eX.symm.trans τ).trans eY, ?_⟩
    rw [← Equiv.prod_comp eX]
    simp

section ph

variable {X Y : Type*} [Fintype X] [DecidableEq Y] {m : ℕ} (y0 : Y)
  (eX : Fin (m + 1) ≃ X) (eY : Fin m ≃ {y // y ≠ y0}) (f : X → {y // y ≠ y0} → M)

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`, case `0 ∈ B`: if `σ` sends `e_A(i_0)` to `0`
and `e_A(i)` to `e_B(σ'(i))` for `i ≠ i_0`, then the product over the pairs `{a, σ(a)}` avoiding
`0` is `Π_{i ≠ i_0} f(e_A(i), e_B(σ'(i)))`. -/
theorem prod_ph_of_eq (σ : X ≃ Y) (i₀ : Fin (m + 1)) (σ' : {i // i ≠ i₀} ≃ Fin m)
    (h₀ : σ (eX i₀) = y0) (h : ∀ i : {i // i ≠ i₀}, σ (eX i) = eY (σ' i)) :
    (∏ x, if h : σ x = y0 then 1 else f x ⟨σ x, h⟩) =
      ∏ i : {i // i ≠ i₀}, f (eX i) (eY (σ' i)) := by
  rw [← Equiv.prod_comp eX, Fintype.prod_eq_mul_prod_subtype_ne _ i₀, dif_pos h₀, one_mul]
  refine Fintype.prod_congr _ _ fun i => ?_
  have hi : σ (eX i) ≠ y0 := by rw [h i]; exact (eY (σ' i)).2
  rw [dif_neg hi]
  congr 1
  exact Subtype.ext (h i)

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`, case `0 ∈ B`: a bijection `σ : A → B` sends
exactly one `i_0` to `0`, the remaining pairs form a bijection `[m+1] ∖ {i_0} → [m]`, and every
pair `(i_0, bijection)` arises. -/
theorem match_ph :
    (∀ σ : X ≃ Y, ∃ (i₀ : Fin (m + 1)) (σ' : {i // i ≠ i₀} ≃ Fin m),
      (∏ x, if h : σ x = y0 then 1 else f x ⟨σ x, h⟩) =
        ∏ i : {i // i ≠ i₀}, f (eX i) (eY (σ' i))) ∧
    (∀ (i₀ : Fin (m + 1)) (σ' : {i // i ≠ i₀} ≃ Fin m), ∃ σ : X ≃ Y,
      (∏ x, if h : σ x = y0 then 1 else f x ⟨σ x, h⟩) =
        ∏ i : {i // i ≠ i₀}, f (eX i) (eY (σ' i))) := by
  constructor
  · intro σ
    set ε := eX.trans σ with hε
    have hiff : ∀ i, i ≠ ε.symm y0 ↔ ε i ≠ y0 := fun i => by
      rw [not_iff_not, Equiv.apply_eq_iff_eq_symm_apply]
    refine ⟨ε.symm y0, (ε.subtypeEquiv hiff).trans eY.symm, ?_⟩
    refine prod_ph_of_eq y0 eX eY f σ _ _ ?_ ?_
    · change ε (ε.symm y0) = y0
      exact ε.apply_symm_apply y0
    · intro i
      simp [Equiv.subtypeEquiv_apply, hε]
  · intro i₀ σ'
    refine ⟨eX.symm.trans ((Equiv.optionSubtypeNe i₀).symm.trans
      ((σ'.trans eY).optionCongr.trans (Equiv.optionSubtypeNe y0))), ?_⟩
    refine prod_ph_of_eq y0 eX eY f _ i₀ σ' ?_ ?_
    · simp
    · intro i
      simp [Equiv.optionSubtypeNe_symm_of_ne i.2]

end ph

end ColPairs

end
