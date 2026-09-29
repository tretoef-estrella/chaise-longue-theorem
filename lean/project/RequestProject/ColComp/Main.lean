module

public import RequestProject.ColComp.Product

/-!
# Lemma 6.3 (iv) and (v) of `q_col_compatible.md`

* `ColComp.lemma63_iv_exists`: a compatible matching exists iff `|𝒞_1|` is even and
  `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`;
* `ColComp.lemma63_iv_card`: in that case there are `(|𝒞_1| − 1)!! · Π_{ζ∈ℛ} |𝒞_ζ|!` of them;
* `ColComp.lemma63_v`, `ColComp.lemma63_v_cExt`: if `Π_v c_v = 1` (e.g. for the colouring
  `cExt c` of `q_col_survivors.md`), compatibility only has to be checked at the pairs avoiding
  `0`.
-/

@[expose] public section

namespace ColComp

open ColSplit ColSurv

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-- **Proof** of Lemma 6.3 (iv) in `q_col_compatible.md`: tuples `(P, (σ_ζ))` exist iff `|𝒞_1|` is
even and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`. -/
theorem nonempty_tuples_iff (c : Fin (2 * k + 2) → F) (R : Finset F) :
    Nonempty (Tuples c R) ↔
      Even (cls c 1).card ∧ ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card := by
  unfold Tuples
  rw [nonempty_prod, PerfMatch.nonempty_perfMatch_iff, Fintype.card_coe, Classical.nonempty_pi]
  refine and_congr Iff.rfl ⟨fun h ζ hζ => ?_, fun h ζ => ?_⟩
  · have := Fintype.card_eq.2 (h ⟨ζ, hζ⟩)
    rwa [Fintype.card_coe, Fintype.card_coe] at this
  · apply Fintype.card_eq.1
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h ζ ζ.2

/-- **Proof** of Lemma 6.3 (iv) in `q_col_compatible.md`: if `|𝒞_1|` is even and
`|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for `ζ ∈ ℛ`, the number of tuples `(P, (σ_ζ))` is
`(|𝒞_1| − 1)!! · Π_{ζ∈ℛ} |𝒞_ζ|!`. -/
theorem card_tuples (c : Fin (2 * k + 2) → F) (R : Finset F) (h1 : Even (cls c 1).card)
    (h2 : ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card) :
    Nat.card (Tuples c R) =
      ((cls c 1).card - 1).doubleFactorial * ∏ ζ ∈ R, ((cls c ζ).card).factorial := by
  unfold Tuples
  rw [Nat.card_prod, PerfMatch.card_perfMatch, Fintype.card_coe, if_pos h1, Nat.card_pi]
  congr 1
  rw [← Finset.prod_coe_sort R]
  refine Finset.prod_congr rfl fun ζ _ => ?_
  have e : cls c (ζ : F) ≃ cls c (ζ : F)⁻¹ :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact h2 ζ ζ.2)
  rw [Nat.card_eq_fintype_card, Fintype.card_equiv e, Fintype.card_coe]

/-- **Lemma 6.3 (iv)** of `q_col_compatible.md` (existence): for a colouring `c : V → μ` and a set
`ℛ` of representatives, a matching compatible with `c` exists iff `|𝒞_1|` is even and
`|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`. -/
theorem lemma63_iv_exists {R : Finset F} (hR : IsReps S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) :
    (∃ J : BallotBound.Matching k, Compatible c J) ↔
      Even (cls c 1).card ∧ ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card := by
  rw [← nonempty_tuples_iff, ← (compEquiv hR hc).nonempty_congr]
  exact ⟨fun ⟨J, hJ⟩ => ⟨⟨J, hJ⟩⟩, fun ⟨J⟩ => ⟨J.1, J.2⟩⟩

/-- **Lemma 6.3 (iv)** of `q_col_compatible.md` (count): if `|𝒞_1|` is even and
`|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ ℛ`, the number of matchings compatible with `c` is
`(|𝒞_1| − 1)!! · Π_{ζ∈ℛ} |𝒞_ζ|!` (with `(−1)!! = 1`, which holds as `(0 − 1)!! = 0!! = 1` in `ℕ`). -/
theorem lemma63_iv_card {R : Finset F} (hR : IsReps S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) (h1 : Even (cls c 1).card)
    (h2 : ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card) :
    Nat.card {J : BallotBound.Matching k // Compatible c J} =
      ((cls c 1).card - 1).doubleFactorial * ∏ ζ ∈ R, ((cls c ζ).card).factorial := by
  rw [← card_tuples c R h1 h2]
  exact Nat.card_congr (compEquiv hR hc)

/-- **Lemma 6.3 (v)** of `q_col_compatible.md` (the pair of `0`): if `Π_{v∈V} c_v = 1`, then `J` is
compatible with `c` iff `c_a c_{J(a)} = 1` for every `a` with `a ≠ 0` and `J(a) ≠ 0`.
(No hypothesis `c : V → μ` is needed here.) -/
theorem lemma63_v {c : Fin (2 * k + 2) → F} (hprod : ∏ v, c v = 1)
    (J : BallotBound.Matching k) :
    Compatible c J ↔ ∀ a, a ≠ 0 → J.1 a ≠ 0 → c a * c (J.1 a) = 1 := by
  refine ⟨fun h a _ _ => h a, fun h => ?_⟩
  have hJ : ∀ a, J.1 (J.1 a) = a := fun a => (J.2 a).2
  have hJ0 : (0 : Fin (2 * k + 2)) ≠ J.1 0 := fun e => (J.2 0).1 e.symm
  have hs : ∏ v ∈ Finset.univ \ {0, J.1 0}, c v = 1 := by
    refine Finset.prod_involution (fun a _ => J.1 a) ?_ (fun a _ _ => (J.2 a).1) ?_
      (fun a _ => hJ a)
    · intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at ha
      refine h a ha.1 fun e => ha.2 ?_
      rw [← e, hJ]
    · intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at ha ⊢
      refine ⟨fun e => ha.2 ?_, fun e => ha.1 ?_⟩
      · rw [← e, hJ]
      · rw [← hJ a, e, hJ]
  have h0 : c 0 * c (J.1 0) = 1 := by
    have := Finset.prod_sdiff (f := c) (Finset.subset_univ ({0, J.1 0} : Finset _))
    rw [hs, one_mul, Finset.prod_pair hJ0, hprod] at this
    exact this
  intro a
  by_cases ha : a = 0
  · rw [ha]; exact h0
  by_cases hb : J.1 a = 0
  · have : a = J.1 0 := by rw [← hb, hJ]
    rw [this, hJ, mul_comm]
    exact h0
  exact h a ha hb

/-- **Lemma 6.3 (v)** of `q_col_compatible.md`, for the colouring `c_0, c_1, …, c_{2k+1}` of
`q_col_survivors.md` (`c ∈ μ^{2k+1}` extended by `c_0 = (c_1 ⋯ c_{2k+1})^{−1}`, so that
`Π_v c_v = 1`): `J` is compatible with it iff `c_a c_{J(a)} = 1` for every `a ≠ 0` with
`J(a) ≠ 0`. -/
theorem lemma63_v_cExt (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k) :
    Compatible (cExt c) J ↔ ∀ a, a ≠ 0 → J.1 a ≠ 0 → cExt c a * cExt c (J.1 a) = 1 :=
  lemma63_v (prod_cExt c) J

end ColComp

end
