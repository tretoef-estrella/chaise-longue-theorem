module

public import RequestProject.ColDecomp.Defs

/-!
# The pairs of a compatible matching (`q_col_decomp.md`, Proof of Proposition 6.5 (ii))

For a compatible matching `J` corresponding to `(P, (σ_ζ))` (Lemma 6.3 (iii)), the pairs of `J`
are the pairs of `P` together with the pairs `{a, σ_ζ(a)}`, `a ∈ 𝒞_ζ`, `ζ ∈ ℛ`, each exactly once
(the classes `𝒞_1`, `𝒞_ζ`, `𝒞_{ζ^{−1}}` partition `V`). This file proves the corresponding
identity of products.
-/

@[expose] public section

namespace ColDecomp

open ColSplit ColSurv ColComp

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-- **Proof** of Proposition 6.5 (ii) in `q_col_decomp.md`: for a matching `J` and a pair
`{a, J(a)}`, the contributions of `a` and of `J(a)` to `Π_{a < J(a)} h(a, J(a))` together give
`h(min(a, J(a)), max(a, J(a)))`. -/
theorem pair_contrib {M : Type*} [CommMonoid M] (J : BallotBound.Matching k)
    (h : Fin (2 * k + 2) → Fin (2 * k + 2) → M) (a : Fin (2 * k + 2)) :
    (if a < J.1 a then h a (J.1 a) else 1) *
        (if J.1 a < J.1 (J.1 a) then h (J.1 a) (J.1 (J.1 a)) else 1) =
      h (min a (J.1 a)) (max a (J.1 a)) := by
  have hJ : J.1 (J.1 a) = a := (J.2 a).2
  rw [hJ]
  rcases lt_or_gt_of_ne (J.2 a).1.symm with hlt | hlt
  · rw [if_pos hlt, if_neg (not_lt.2 hlt.le), mul_one, min_eq_left hlt.le, max_eq_right hlt.le]
  · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, one_mul, min_eq_right hlt.le, max_eq_left hlt.le]

/-- **Proof** of Proposition 6.5 (ii) in `q_col_decomp.md`: for a matching `J` compatible with a
colouring `c : V → μ`, corresponding to `(P, (σ_ζ))` by Lemma 6.3 (iii), the product over the pairs
of `J` splits as the product over the pairs `{a < P(a)}` of `P` times the products over the pairs
`{a, σ_ζ(a)}`, `a ∈ 𝒞_ζ`, `ζ ∈ ℛ`:
`Π_{a<J(a)} h(a, J(a)) = Π_{a<P(a)} h(a, P(a)) · Π_{ζ∈ℛ} Π_{a∈𝒞_ζ} h(min(a,σ_ζ(a)), max(a,σ_ζ(a)))`. -/
theorem prod_pairs_split {M : Type*} [CommMonoid M] {R : Finset F} (hR : IsReps S R)
    {c : Fin (2 * k + 2) → F} (hc : ∀ v, c v ∈ S.μ) (J : CompMatching c)
    (h : Fin (2 * k + 2) → Fin (2 * k + 2) → M) :
    ∏ a ∈ Finset.univ.filter (fun a => a < J.1.1 a), h a (J.1.1 a) =
      (∏ x ∈ Finset.univ.filter (fun x => x.1 < ((restrict c R J).1.1 x).1),
          h x.1 ((restrict c R J).1.1 x).1) *
        ∏ ζ : R, ∏ a : cls c ζ,
          h (min a.1 ((restrict c R J).2 ζ a).1) (max a.1 ((restrict c R J).2 ζ a).1) := by
  set H : Fin (2 * k + 2) → M := fun a => if a < J.1.1 a then h a (J.1.1 a) else 1
  have hpart := lemma63_i_partition hR hc
  rw [Finset.prod_filter]
  change ∏ a, H a = _
  rw [← hpart.2.2, Finset.prod_union (Finset.disjoint_biUnion_right _ _ _ |>.2 hpart.1),
    Finset.prod_biUnion (fun ζ hζ η hη hne => hpart.2.1 ζ hζ η hη hne)]
  congr 1
  · rw [Finset.prod_filter, ← Finset.prod_coe_sort (cls c 1)]
    rfl
  · rw [← Finset.prod_coe_sort R]
    refine Finset.prod_congr rfl fun ζ _ => ?_
    have e : ∏ x ∈ cls c (ζ : F)⁻¹, H x = ∏ x ∈ cls c (ζ : F), H (J.1.1 x) := by
      rw [← J.2.image_cls (ζ : F), Finset.prod_image (fun x _ y _ hxy => by
        rw [← (J.1.2 x).2, hxy, (J.1.2 y).2])]
    change _ = ∏ a : cls c (ζ : F), h (min a.1 (J.1.1 a)) (max a.1 (J.1.1 a))
    rw [Finset.prod_union (lemma63_i_disjoint hR ζ.2 c).1, e,
      ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort (cls c (ζ : F))]
    exact Finset.prod_congr rfl fun a _ => pair_contrib J.1 h a

end ColDecomp

end
