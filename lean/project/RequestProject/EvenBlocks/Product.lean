module

public import RequestProject.EvenBlocks.SelfInv

/-!
# Part A of `q_even_blocks.md`: compatible matchings as product choices, (A8) and (A9)

* `EvenBlocks.Tuples2 S c R`: tuples `((P_ζ)_{ζ∈SInv S}, (σ_ζ)_{ζ∈R})`, `P_ζ` a perfect matching
  of `𝒞_ζ`, `σ_ζ : 𝒞_ζ ≃ 𝒞_{ζ^{−1}}`;
* (A8) `restrict2`, `assemble2`, `compEquiv2`: restriction is a bijection
  `CompMatching c ≃ Tuples2 S c R` with explicit inverse (modelled on `ColComp.compEquiv`);
* (A9) `existsA9`, `cardA9`: existence and number of compatible matchings.
-/

@[expose] public section

namespace EvenBlocks

open ColSplit ColSurv ColComp

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Part A, (A8)** of `q_even_blocks.md`: the tuples
`((P_ζ)_{ζ ∈ SInv S}, (σ_ζ)_{ζ ∈ R})`, `P_ζ` a perfect matching (fixed-point-free involution) of
`𝒞_ζ` and `σ_ζ : 𝒞_ζ → 𝒞_{ζ^{−1}}` a bijection. -/
def Tuples2 (c : Fin (2 * k + 2) → F) (R : Finset F) : Type _ :=
  ((ζ : SInv S) → PerfMatch (cls c (ζ : F))) × ((ζ : R) → (cls c (ζ : F) ≃ cls c (ζ : F)⁻¹))

variable {S}

/-- **Part A, (A8)** of `q_even_blocks.md` (proof): a compatible matching maps the class `𝒞_ζ` of a
self-inverse colour into itself. -/
theorem Compatible.map_cls_SInv {c : Fin (2 * k + 2) → F} {J : BallotBound.Matching k}
    (h : Compatible c J) {ζ : F} (hζ : ζ ∈ SInv S) {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ) :
    J.1 v ∈ cls c ζ := by
  have := h.map_cls hv
  rwa [inv_eq_of_mem_SInv hζ] at this

variable (S) in
/-- **Part A, (A8)** of `q_even_blocks.md`: the restriction map
`J ↦ ((J|_{𝒞_ζ})_{ζ ∈ SInv S}, (J|_{𝒞_ζ})_{ζ ∈ R})`. -/
def restrict2 (c : Fin (2 * k + 2) → F) (R : Finset F) (J : CompMatching c) : Tuples2 S c R :=
  (fun ζ => ⟨fun v => ⟨J.1.1 v, Compatible.map_cls_SInv J.2 ζ.2 v.2⟩,
      fun v => ⟨fun h => (J.1.2 v).1 (congrArg Subtype.val h), Subtype.ext (J.1.2 v).2⟩⟩,
    fun ζ =>
      { toFun := fun v => ⟨J.1.1 v, J.2.map_cls v.2⟩
        invFun := fun v => ⟨J.1.1 v, by simpa using J.2.map_cls v.2⟩
        left_inv := fun v => Subtype.ext (J.1.2 v).2
        right_inv := fun v => Subtype.ext (J.1.2 v).2 })

/-- **Part A, (A8)** of `q_even_blocks.md` (the explicit inverse): the map of `V` that is `P_ζ` on
`𝒞_ζ` (`ζ ∈ SInv S`), `σ_ζ` on `𝒞_ζ` and `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}` (`ζ ∈ R`); the identity on
points of no class (there are none for a colouring with values in `μ`). -/
noncomputable def assembleFun2 (c : Fin (2 * k + 2) → F) (R : Finset F) (t : Tuples2 S c R)
    (v : Fin (2 * k + 2)) : Fin (2 * k + 2) :=
  if h1 : c v ∈ SInv S then ((t.1 ⟨c v, h1⟩).1 ⟨v, mem_cls.2 rfl⟩).1
  else if h2 : c v ∈ R then (t.2 ⟨c v, h2⟩ ⟨v, mem_cls.2 rfl⟩).1
  else if h3 : (c v)⁻¹ ∈ R then ((t.2 ⟨(c v)⁻¹, h3⟩).symm ⟨v, mem_cls.2 (inv_inv _).symm⟩).1
  else v

variable {R : Finset F} {c : Fin (2 * k + 2) → F}

/-- **Part A, (A8)** of `q_even_blocks.md`: the assembled map is `P_ζ` on `𝒞_ζ`,
`ζ ∈ SInv S`. -/
theorem assembleFun2_sinv (t : Tuples2 S c R) {ζ : F} (hζ : ζ ∈ SInv S)
    {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ) :
    assembleFun2 c R t v = ((t.1 ⟨ζ, hζ⟩).1 ⟨v, hv⟩).1 := by
  have e : c v = ζ := mem_cls.1 hv
  subst e
  rw [assembleFun2, dif_pos hζ]

/-- **Part A, (A8)** of `q_even_blocks.md`: the assembled map is `σ_ζ` on `𝒞_ζ`, `ζ ∈ R`. -/
theorem assembleFun2_rep (hR : IsReps2 S R) (t : Tuples2 S c R) {ζ : F} (hζ : ζ ∈ R)
    {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ) :
    assembleFun2 c R t v = (t.2 ⟨ζ, hζ⟩ ⟨v, hv⟩).1 := by
  have e : c v = ζ := mem_cls.1 hv
  subst e
  rw [assembleFun2, dif_neg (hR.mem hζ).2.1, dif_pos hζ]

/-- **Part A, (A8)** of `q_even_blocks.md`: the assembled map is `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}`,
`ζ ∈ R`. -/
theorem assembleFun2_inv (hR : IsReps2 S R) (t : Tuples2 S c R) {ζ : F} (hζ : ζ ∈ R)
    {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ⁻¹) :
    assembleFun2 c R t v = ((t.2 ⟨ζ, hζ⟩).symm ⟨v, hv⟩).1 := by
  have e : ζ = (c v)⁻¹ := by rw [mem_cls.1 hv, inv_inv]
  subst e
  have h := hR.mem hζ
  rw [inv_inv] at h
  rw [assembleFun2, dif_neg h.2.2.1, dif_neg h.2.2.2.1, dif_pos hζ]

/-- **Part A, (A8)** of `q_even_blocks.md` (proof): the assembled map is a fixed-point-free
involution of `V` compatible with `c`. -/
theorem assembleFun2_spec (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples2 S c R)
    (v : Fin (2 * k + 2)) :
    assembleFun2 c R t v ≠ v ∧ assembleFun2 c R t (assembleFun2 c R t v) = v ∧
      c v * c (assembleFun2 c R t v) = 1 := by
  rcases hR.cases (hc v) with h | h | h
  · have hv : v ∈ cls c (c v) := mem_cls.2 rfl
    rw [assembleFun2_sinv t h hv, assembleFun2_sinv t h ((t.1 ⟨c v, h⟩).1 ⟨v, hv⟩).2]
    refine ⟨fun e => ((t.1 ⟨c v, h⟩).2 ⟨v, hv⟩).1 (Subtype.ext e),
      congrArg Subtype.val ((t.1 ⟨c v, h⟩).2 ⟨v, hv⟩).2, ?_⟩
    rw [mem_cls.1 ((t.1 ⟨c v, h⟩).1 ⟨v, hv⟩).2, ← sq]
    exact (mem_SInv_iff.1 h).2
  · have hv : v ∈ cls c (c v) := mem_cls.2 rfl
    rw [assembleFun2_rep hR t h hv, assembleFun2_inv hR t h (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2]
    refine ⟨fun e => ?_, by simp, ?_⟩
    · have h1 := mem_cls.1 (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2
      rw [e] at h1
      exact (hR.mem h).2.2.2.2 h1.symm
    · rw [mem_cls.1 (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc v))]
  · have hv : v ∈ cls c (c v)⁻¹⁻¹ := mem_cls.2 (inv_inv _).symm
    rw [assembleFun2_inv hR t h hv, assembleFun2_rep hR t h ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2]
    refine ⟨fun e => ?_, by simp, ?_⟩
    · have h1 := mem_cls.1 ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2
      rw [e] at h1
      exact (hR.mem h).2.2.2.2 (by rw [inv_inv]; exact h1)
    · rw [mem_cls.1 ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2,
        mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc v))]

/-- **Part A, (A8)** of `q_even_blocks.md` (the explicit inverse map): the compatible matching
assembled from `((P_ζ), (σ_ζ))`. -/
noncomputable def assemble2 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples2 S c R) :
    CompMatching c :=
  ⟨⟨assembleFun2 c R t, fun v =>
      ⟨(assembleFun2_spec hR hc t v).1, (assembleFun2_spec hR hc t v).2.1⟩⟩,
    fun v => (assembleFun2_spec hR hc t v).2.2⟩

/-- **Part A, (A8)** of `q_even_blocks.md`: assembling the restrictions of a compatible matching
gives it back. -/
theorem assemble2_restrict2 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) (J : CompMatching c) :
    assemble2 hR hc (restrict2 S c R J) = J := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change assembleFun2 c R (restrict2 S c R J) v = J.1.1 v
  rcases hR.cases (hc v) with h | h | h
  · rw [assembleFun2_sinv _ h (mem_cls.2 rfl)]; rfl
  · rw [assembleFun2_rep hR _ h (mem_cls.2 rfl)]; rfl
  · rw [assembleFun2_inv hR _ h (mem_cls.2 (inv_inv _).symm)]; rfl

/-- **Part A, (A8)** of `q_even_blocks.md`: the restrictions of the matching assembled from
`((P_ζ), (σ_ζ))` are the `P_ζ` and the `σ_ζ`. -/
theorem restrict2_assemble2 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples2 S c R) :
    restrict2 S c R (assemble2 hR hc t) = t := by
  obtain ⟨P, σ⟩ := t
  refine Prod.ext (funext fun ζ => PerfMatch.ext fun v => Subtype.ext ?_)
    (funext fun ζ => Equiv.ext fun v => Subtype.ext ?_)
  · exact assembleFun2_sinv (P, σ) ζ.2 v.2
  · exact assembleFun2_rep hR (P, σ) ζ.2 v.2

/-- **Part A, (A8)** of `q_even_blocks.md`: for a colouring `c : V → μ` and `IsReps2 S R`,
restriction is a bijection
`CompMatching c ≃ ((ζ : SInv S) → PerfMatch 𝒞_ζ) × ((ζ : R) → (𝒞_ζ ≃ 𝒞_{ζ^{−1}}))`,
with the explicit inverse `assemble2` (as `ColComp.compEquiv`). -/
noncomputable def compEquiv2 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) :
    CompMatching c ≃ Tuples2 S c R where
  toFun := restrict2 S c R
  invFun := assemble2 hR hc
  left_inv := assemble2_restrict2 hR hc
  right_inv := restrict2_assemble2 hR hc

/-- **Part A, (A9)** of `q_even_blocks.md` (proof): tuples `((P_ζ), (σ_ζ))` exist iff every class
of a self-inverse colour has even size and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for `ζ ∈ R`. -/
theorem nonempty_tuples2_iff (c : Fin (2 * k + 2) → F) (R : Finset F) :
    Nonempty (Tuples2 S c R) ↔
      (∀ ζ ∈ SInv S, Even (cls c ζ).card) ∧ ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card := by
  unfold Tuples2
  rw [nonempty_prod, Classical.nonempty_pi, Classical.nonempty_pi]
  refine and_congr ⟨fun h ζ hζ => ?_, fun h ζ => ?_⟩ ⟨fun h ζ hζ => ?_, fun h ζ => ?_⟩
  · have := PerfMatch.nonempty_perfMatch_iff.1 (h ⟨ζ, hζ⟩)
    rwa [Fintype.card_coe] at this
  · rw [PerfMatch.nonempty_perfMatch_iff, Fintype.card_coe]
    exact h ζ ζ.2
  · have := Fintype.card_eq.2 (h ⟨ζ, hζ⟩)
    rwa [Fintype.card_coe, Fintype.card_coe] at this
  · apply Fintype.card_eq.1
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h ζ ζ.2

/-- **Part A, (A9)** of `q_even_blocks.md` (proof): under the conditions of (A9), the number of
tuples is `Π_{ζ∈SInv S} (|𝒞_ζ| − 1)!! · Π_{ζ∈R} |𝒞_ζ|!`. -/
theorem card_tuples2 (c : Fin (2 * k + 2) → F) (R : Finset F)
    (h1 : ∀ ζ ∈ SInv S, Even (cls c ζ).card)
    (h2 : ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card) :
    Nat.card (Tuples2 S c R) =
      (∏ ζ ∈ SInv S, ((cls c ζ).card - 1).doubleFactorial) *
        ∏ ζ ∈ R, ((cls c ζ).card).factorial := by
  unfold Tuples2
  rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
  congr 1
  · rw [← Finset.prod_coe_sort (SInv S)]
    refine Finset.prod_congr rfl fun ζ _ => ?_
    rw [PerfMatch.card_perfMatch, Fintype.card_coe, if_pos (h1 ζ ζ.2)]
  · rw [← Finset.prod_coe_sort R]
    refine Finset.prod_congr rfl fun ζ _ => ?_
    have e : cls c (ζ : F) ≃ cls c (ζ : F)⁻¹ :=
      Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact h2 ζ ζ.2)
    rw [Nat.card_eq_fintype_card, Fintype.card_equiv e, Fintype.card_coe]

/-- **Part A, (A9)** of `q_even_blocks.md` (existence): for a colouring `c : V → μ` and
`IsReps2 S R`, a matching compatible with `c` exists iff `|𝒞_ζ|` is even for every self-inverse
colour `ζ` and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|` for every `ζ ∈ R`. -/
theorem existsA9 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ) :
    (∃ J : BallotBound.Matching k, Compatible c J) ↔
      (∀ ζ ∈ SInv S, Even (cls c ζ).card) ∧ ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card := by
  rw [← nonempty_tuples2_iff, ← (compEquiv2 hR hc).nonempty_congr]
  exact ⟨fun ⟨J, hJ⟩ => ⟨⟨J, hJ⟩⟩, fun ⟨J⟩ => ⟨J.1, J.2⟩⟩

/-- **Part A, (A9)** of `q_even_blocks.md` (count): under the conditions of (A9), the number of
matchings compatible with `c` is `Π_{ζ∈SInv S} (|𝒞_ζ| − 1)!! · Π_{ζ∈R} |𝒞_ζ|!` (with
`(−1)!! = 1`, as `(0 − 1)!! = 0!! = 1` in `ℕ`). -/
theorem cardA9 (hR : IsReps2 S R) (hc : ∀ v, c v ∈ S.μ)
    (h1 : ∀ ζ ∈ SInv S, Even (cls c ζ).card)
    (h2 : ∀ ζ ∈ R, (cls c ζ).card = (cls c ζ⁻¹).card) :
    Nat.card {J : BallotBound.Matching k // Compatible c J} =
      (∏ ζ ∈ SInv S, ((cls c ζ).card - 1).doubleFactorial) *
        ∏ ζ ∈ R, ((cls c ζ).card).factorial := by
  rw [← card_tuples2 c R h1 h2]
  exact Nat.card_congr (compEquiv2 hR hc)

end EvenBlocks

end
