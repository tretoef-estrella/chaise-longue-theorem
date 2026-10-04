module

public import RequestProject.EvenBlocks.Product

/-!
# Part B of `q_even_blocks.md`: the self-inverse blocks and the generator form (B1)

* `EvenBlocks.WS`, `EvenBlocks.gPS`, `EvenBlocks.IcS`: the block of variables, the block
  generators and the block ideal of a self-inverse colour `ζ` (with `W1 S c = WS S c 1`,
  `gP S c = gPS S c 1`, `Ic1 S c = IcS S c 1`, all by `rfl`);
* `EvenBlocks.prod_pairs_split2`: the product over the pairs of a compatible matching splits along
  the blocks (modelled on `ColDecomp.prod_pairs_split`);
* (B1) `EvenBlocks.piC_psi_eq_unit_mul2`: the generator form of `π_c(ψ_J)`.
-/

@[expose] public section

open MvPolynomial

namespace EvenBlocks

open ColSplit ColSurv ColComp ColTensor ColDecomp

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Part B, Definitions** of `q_even_blocks.md`: for a colour `ζ` (used for `ζ ∈ SInv S`), the
block of variables `W_ζ^S := 𝒞_ζ ∖ {0}`, i.e. `varSet (cls (cExt c) ζ)`. -/
noncomputable def WS (c : Fin (2 * k + 1) → S.μ) (ζ : F) : Finset (Fin (2 * k + 1)) :=
  varSet (cls (cExt c) ζ)

/-- **Part B, Definitions** of `q_even_blocks.md`: for a colour `ζ` (used for `ζ ∈ SInv S`) and
a perfect matching `P` of `𝒞_ζ`, the block generator `g_P ∈ B(W_ζ^S)`: the product of
`f_{a,b} = pairF S.q (tB S c (WS S c ζ)) a b` over the pairs `{a < b = P(a)}` of `P` — exactly
`ColDecomp.gP` with the class `ζ` in place of the class `1`. -/
noncomputable def gPS (c : Fin (2 * k + 1) → S.μ) (ζ : F) (P : PerfMatch (cls (cExt c) ζ)) :
    (boxS S c).Box (WS S c ζ) :=
  ∏ x ∈ Finset.univ.filter (fun x => x.1 < (P.1 x).1),
    pairF S.q (tB S c (WS S c ζ)) x.1 (P.1 x).1

/-- **Part B, Definitions** of `q_even_blocks.md`: the block ideal
`I_{c,ζ}^S := (g_P : P a perfect matching of 𝒞_ζ) ⊆ B(W_ζ^S)`. -/
noncomputable def IcS (c : Fin (2 * k + 1) → S.μ) (ζ : F) : Ideal ((boxS S c).Box (WS S c ζ)) :=
  Ideal.span (Set.range (gPS S c ζ))

/-- **Part B, Definitions** of `q_even_blocks.md`: `W1 S c = WS S c 1` (by `rfl`). -/
theorem W1_eq_WS (c : Fin (2 * k + 1) → S.μ) : W1 S c = WS S c 1 := rfl

/-- **Part B, Definitions** of `q_even_blocks.md`: `gP S c = gPS S c 1` (by `rfl`). -/
theorem gP_eq_gPS (c : Fin (2 * k + 1) → S.μ) : gP S c = gPS S c 1 := rfl

/-- **Part B, Definitions** of `q_even_blocks.md`: `Ic1 S c = IcS S c 1` (by `rfl`). -/
theorem Ic1_eq_IcS (c : Fin (2 * k + 1) → S.μ) : Ic1 S c = IcS S c 1 := rfl

/-- **Part B, (B1)** of `q_even_blocks.md` (proof): `ι_{W_ζ^S}(g_P)` is the product of the
`f_{a,b}` over the pairs `{a < b}` of `P`, computed in `B({1, …, d})` (as `ColDecomp.iota_gP`). -/
theorem iota_gPS (c : Fin (2 * k + 1) → S.μ) (ζ : F) (P : PerfMatch (cls (cExt c) ζ)) :
    (boxS S c).iota (WS S c ζ) Finset.univ (Finset.subset_univ _) (gPS S c ζ P) =
      ∏ x ∈ Finset.univ.filter (fun x => x.1 < (P.1 x).1),
        pairF S.q (tB S c Finset.univ) x.1 (P.1 x).1 := by
  rw [gPS, map_prod]
  refine Finset.prod_congr rfl fun x _ => map_pairF _ _ _ _ _ _ ?_ ?_
  · exact iota_tB S c _ _ fun j hj => by
      simp only [WS, varSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hj]; exact x.2
  · exact iota_tB S c _ _ fun j hj => by
      simp only [WS, varSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hj]; exact (P.1 x).2

variable {S}

/-- **Part B, (B1)** of `q_even_blocks.md` (proof; model `ColDecomp.prod_pairs_split`): for a
matching `J` compatible with `c : V → μ`, with image `((P_ζ), (σ_ζ))` under (A8), the product over
the pairs of `J` splits as the product over the self-inverse colours `ζ` of the products over the
pairs `{a < P_ζ(a)}`, times the products over `ζ ∈ R`, `a ∈ 𝒞_ζ` of the pairs `{a, σ_ζ(a)}`. -/
theorem prod_pairs_split2 {M : Type*} [CommMonoid M] {R : Finset F} (hR : IsReps2 S R)
    {c : Fin (2 * k + 2) → F} (hc : ∀ v, c v ∈ S.μ) (J : CompMatching c)
    (h : Fin (2 * k + 2) → Fin (2 * k + 2) → M) :
    ∏ a ∈ Finset.univ.filter (fun a => a < J.1.1 a), h a (J.1.1 a) =
      (∏ ζ : SInv S, ∏ x ∈ Finset.univ.filter
          (fun x => x.1 < (((restrict2 S c R J).1 ζ).1 x).1),
          h x.1 (((restrict2 S c R J).1 ζ).1 x).1) *
        ∏ ζ : R, ∏ a : cls c ζ,
          h (min a.1 ((restrict2 S c R J).2 ζ a).1) (max a.1 ((restrict2 S c R J).2 ζ a).1) := by
  set H : Fin (2 * k + 2) → M := fun a => if a < J.1.1 a then h a (J.1.1 a) else 1
  obtain ⟨hA, hB, hC, hD, hU⟩ := partitionA5 hR hc
  rw [Finset.prod_filter]
  change ∏ a, H a = _
  rw [← hU, Finset.prod_union (Finset.disjoint_biUnion_left _ _ _ |>.2 fun ζ hζ =>
      Finset.disjoint_biUnion_right _ _ _ |>.2 fun η hη => hB ζ hζ η hη),
    Finset.prod_biUnion (fun ζ hζ η hη hne => hA ζ hζ η hη hne),
    Finset.prod_biUnion (fun ζ hζ η hη hne => hD ζ hζ η hη hne)]
  congr 1
  · rw [← Finset.prod_coe_sort (SInv S)]
    refine Finset.prod_congr rfl fun ζ _ => ?_
    rw [Finset.prod_filter, ← Finset.prod_coe_sort (cls c (ζ : F))]
    rfl
  · rw [← Finset.prod_coe_sort R]
    refine Finset.prod_congr rfl fun ζ _ => ?_
    have e : ∏ x ∈ cls c (ζ : F)⁻¹, H x = ∏ x ∈ cls c (ζ : F), H (J.1.1 x) := by
      rw [← J.2.image_cls (ζ : F), Finset.prod_image (fun x _ y _ hxy => by
        rw [← (J.1.2 x).2, hxy, (J.1.2 y).2])]
    change _ = ∏ a : cls c (ζ : F), h (min a.1 (J.1.1 a)) (max a.1 (J.1.1 a))
    rw [Finset.prod_union (hC ζ ζ.2), e,
      ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort (cls c (ζ : F))]
    exact Finset.prod_congr rfl fun a _ => pair_contrib J.1 h a

variable (S)

/-- **Part B, (B1)** of `q_even_blocks.md`: for `IsReps2 S R` and a matching `J` compatible with
`cExt c`, with image `((P_ζ)_{ζ∈SInv S}, (σ_ζ)_{ζ∈R})` under (A8), `π_c(ψ_J)` read in
`B({1, …, d})` through `rcEquiv` is a unit times
`Π_{ζ ∈ SInv S} ι(g_{P_ζ}) · Π_{ζ ∈ R} ι(g_{σ_ζ})`, where `ι = ι_{W,{1,…,d}}`
(model: `ColDecomp.piC_psi_eq_unit_mul`). -/
theorem piC_psi_eq_unit_mul2 (c : Fin (2 * k + 1) → S.μ) {R : Finset F} (hR : IsReps2 S R)
    (J : CompMatching (cExt c)) :
    ∃ w : ((boxS S c).Box Finset.univ)ˣ,
      rcEquiv (boxS S c) (S.piC c (psi S k J.1)) =
        w * ((∏ ζ : SInv S, (boxS S c).iota (WS S c ζ) Finset.univ (Finset.subset_univ _)
            (gPS S c ζ ((restrict2 S (cExt c) R J).1 ζ))) *
          ∏ ζ : R, (boxS S c).iota (Wz S c ζ) Finset.univ (Finset.subset_univ _)
            (gσ S c ζ ((restrict2 S (cExt c) R J).2 ζ))) := by
  obtain ⟨w, hw⟩ := piC_psi_eq_unit_mul_prod S c J.1 J.2
  refine ⟨w, ?_⟩
  rw [hw, prod_pairs_split2 hR (cExt_mem c) J (pairF S.q (tB S c Finset.univ))]
  simp_rw [iota_gPS, iota_gσ]

end EvenBlocks

end
