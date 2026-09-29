module

public import RequestProject.ColComp.Defs
public import RequestProject.ColComp.PerfMatch

/-!
# Lemma 6.3 (iii) of `q_col_compatible.md`: compatible matchings are product choices

* `ColComp.lemma63_iii_compatible_iff`: `J` is compatible iff `J(𝒞_1) = 𝒞_1` and
  `J(𝒞_ζ) = 𝒞_{ζ^{−1}}` for `ζ ∈ ℛ`;
* `ColComp.restrict`: the map `J ↦ (J|_{𝒞_1}, (J|_{𝒞_ζ})_{ζ ∈ ℛ})`;
* `ColComp.assemble`: the involution assembled from `(P, (σ_ζ))`;
* `ColComp.lemma63_iii_assemble_restrict`, `ColComp.lemma63_iii_restrict_assemble`,
  `ColComp.lemma63_iii_bijective`: the two maps are mutually inverse bijections.
-/

@[expose] public section

namespace ColComp

open ColSplit ColSurv

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the set of matchings of `V` compatible with
`c`. -/
def CompMatching (c : Fin (2 * k + 2) → F) : Type :=
  {J : BallotBound.Matching k // Compatible c J}

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the set of tuples `(P, (σ_ζ)_{ζ∈ℛ})` with `P` a
perfect matching (fixed-point-free involution) of `𝒞_1` and `σ_ζ : 𝒞_ζ → 𝒞_{ζ^{−1}}` a bijection
for each `ζ ∈ ℛ`. -/
def Tuples (c : Fin (2 * k + 2) → F) (R : Finset F) : Type _ :=
  PerfMatch (cls c 1) × ((ζ : R) → (cls c (ζ : F) ≃ cls c (ζ : F)⁻¹))

/-- **Proof** of Lemma 6.3 (iii) in `q_col_compatible.md`: if `J` is compatible, then
`c_{J(a)} = c_a^{−1}`, so `J` maps `𝒞_ζ` into `𝒞_{ζ^{−1}}` for every `ζ`. -/
theorem Compatible.map_cls {c : Fin (2 * k + 2) → F} {J : BallotBound.Matching k}
    (h : Compatible c J) {ζ : F} {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ) :
    J.1 v ∈ cls c ζ⁻¹ := by
  rw [mem_cls] at *
  rw [← hv]
  exact eq_inv_of_mul_eq_one_right (h v)

/-- **Proof** of Lemma 6.3 (iii) in `q_col_compatible.md`: if `J` is compatible, then
`J(𝒞_ζ) = 𝒞_{ζ^{−1}}` for every `ζ` (as `J` is an involution). -/
theorem Compatible.image_cls {c : Fin (2 * k + 2) → F} {J : BallotBound.Matching k}
    (h : Compatible c J) (ζ : F) : (cls c ζ).image J.1 = cls c ζ⁻¹ := by
  ext w
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact h.map_cls hv
  · intro hw
    refine ⟨J.1 w, ?_, (J.2 w).2⟩
    simpa using h.map_cls hw

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (first claim): for a colouring `c : V → μ` and a
set `ℛ` of representatives, a matching `J` is compatible with `c` iff `J(𝒞_1) = 𝒞_1` and
`J(𝒞_ζ) = 𝒞_{ζ^{−1}}` for every `ζ ∈ ℛ`. -/
theorem lemma63_iii_compatible_iff {R : Finset F} (hR : IsReps S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) (J : BallotBound.Matching k) :
    Compatible c J ↔ (cls c 1).image J.1 = cls c 1 ∧ ∀ ζ ∈ R, (cls c ζ).image J.1 = cls c ζ⁻¹ := by
  constructor
  · intro h
    exact ⟨by simpa using h.image_cls 1, fun ζ _ => h.image_cls ζ⟩
  · rintro ⟨h1, h2⟩ a
    rcases hR.cases (hc a) with ha | ha | ha
    · have : J.1 a ∈ cls c 1 := h1 ▸ Finset.mem_image_of_mem _ (mem_cls.2 ha)
      rw [mem_cls] at this
      rw [ha, this, one_mul]
    · have : J.1 a ∈ cls c (c a)⁻¹ := h2 _ ha ▸ Finset.mem_image_of_mem _ (mem_cls.2 rfl)
      rw [mem_cls] at this
      rw [this, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc a))]
    · have hmem : a ∈ cls c (c a)⁻¹⁻¹ := mem_cls.2 (inv_inv _).symm
      rw [← h2 _ ha, Finset.mem_image] at hmem
      obtain ⟨b, hb, hba⟩ := hmem
      have : J.1 a = b := by rw [← hba, (J.2 b).2]
      rw [this, mem_cls.1 hb, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc a))]

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the restriction map
`J ↦ (J|_{𝒞_1}, (J|_{𝒞_ζ})_{ζ ∈ ℛ})` from compatible matchings to tuples `(P, (σ_ζ))`. -/
def restrict (c : Fin (2 * k + 2) → F) (R : Finset F) (J : CompMatching c) : Tuples c R :=
  (⟨fun v => ⟨J.1.1 v, by simpa using J.2.map_cls v.2⟩,
      fun v => ⟨fun h => (J.1.2 v).1 (congrArg Subtype.val h), Subtype.ext (J.1.2 v).2⟩⟩,
    fun ζ =>
      { toFun := fun v => ⟨J.1.1 v, J.2.map_cls v.2⟩
        invFun := fun v => ⟨J.1.1 v, by simpa using J.2.map_cls v.2⟩
        left_inv := fun v => Subtype.ext (J.1.2 v).2
        right_inv := fun v => Subtype.ext (J.1.2 v).2 })

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (the inverse map): the map of `V` that is `P` on
`𝒞_1`, `σ_ζ` on `𝒞_ζ` and `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`).  (On points of no class, which do
not exist for a colouring with values in `μ`, it is the identity.) -/
noncomputable def assembleFun (c : Fin (2 * k + 2) → F) (R : Finset F) (t : Tuples c R)
    (v : Fin (2 * k + 2)) : Fin (2 * k + 2) :=
  if h1 : c v = 1 then (t.1.1 ⟨v, mem_cls.2 h1⟩).1
  else if h2 : c v ∈ R then (t.2 ⟨c v, h2⟩ ⟨v, mem_cls.2 rfl⟩).1
  else if h3 : (c v)⁻¹ ∈ R then ((t.2 ⟨(c v)⁻¹, h3⟩).symm ⟨v, mem_cls.2 (inv_inv _).symm⟩).1
  else v

variable {R : Finset F} {c : Fin (2 * k + 2) → F}

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the assembled map is `P` on `𝒞_1`. -/
theorem assembleFun_one (t : Tuples c R) {v : Fin (2 * k + 2)} (hv : v ∈ cls c 1) :
    assembleFun c R t v = (t.1.1 ⟨v, hv⟩).1 := by
  rw [assembleFun, dif_pos (mem_cls.1 hv)]

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the assembled map is `σ_ζ` on `𝒞_ζ`
(`ζ ∈ ℛ`). -/
theorem assembleFun_rep (hR : IsReps S R) (t : Tuples c R) {ζ : F} (hζ : ζ ∈ R)
    {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ) :
    assembleFun c R t v = (t.2 ⟨ζ, hζ⟩ ⟨v, hv⟩).1 := by
  have e : c v = ζ := mem_cls.1 hv
  subst e
  rw [assembleFun, dif_neg (hR.mem hζ).2.1, dif_pos hζ]

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the assembled map is `σ_ζ^{−1}` on
`𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`). -/
theorem assembleFun_inv (hR : IsReps S R) (t : Tuples c R) {ζ : F} (hζ : ζ ∈ R)
    {v : Fin (2 * k + 2)} (hv : v ∈ cls c ζ⁻¹) :
    assembleFun c R t v = ((t.2 ⟨ζ, hζ⟩).symm ⟨v, hv⟩).1 := by
  have e : ζ = (c v)⁻¹ := by rw [mem_cls.1 hv, inv_inv]
  subst e
  have h1 : c v ≠ 1 := fun h => (hR.mem hζ).2.1 (by rw [h, inv_one])
  have h2 : c v ∉ R := by
    have := (hR.mem hζ).2.2
    rwa [inv_inv] at this
  rw [assembleFun, dif_neg h1, dif_neg h2, dif_pos hζ]

/-- **Proof** of Lemma 6.3 (iii) in `q_col_compatible.md`: the assembled map is a
fixed-point-free involution of `V` compatible with `c`. -/
theorem assembleFun_spec (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples c R)
    (v : Fin (2 * k + 2)) :
    assembleFun c R t v ≠ v ∧ assembleFun c R t (assembleFun c R t v) = v ∧
      c v * c (assembleFun c R t v) = 1 := by
  rcases hR.cases (hc v) with h | h | h
  · have hv : v ∈ cls c 1 := mem_cls.2 h
    rw [assembleFun_one t hv, assembleFun_one t (t.1.1 ⟨v, hv⟩).2]
    refine ⟨fun e => (t.1.2 ⟨v, hv⟩).1 (Subtype.ext e), congrArg Subtype.val (t.1.2 ⟨v, hv⟩).2,
      ?_⟩
    rw [h, mem_cls.1 (t.1.1 ⟨v, hv⟩).2, one_mul]
  · have hv : v ∈ cls c (c v) := mem_cls.2 rfl
    rw [assembleFun_rep hR t h hv, assembleFun_inv hR t h (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2]
    refine ⟨fun e => ?_, by simp, ?_⟩
    · have h1 := mem_cls.1 (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2
      rw [e] at h1
      exact hR.inv_ne h h1.symm
    · rw [mem_cls.1 (t.2 ⟨c v, h⟩ ⟨v, hv⟩).2, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc v))]
  · have hv : v ∈ cls c (c v)⁻¹⁻¹ := mem_cls.2 (inv_inv _).symm
    rw [assembleFun_inv hR t h hv, assembleFun_rep hR t h ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2]
    refine ⟨fun e => ?_, by simp, ?_⟩
    · have h1 := mem_cls.1 ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2
      rw [e] at h1
      exact hR.inv_ne h (by rw [inv_inv]; exact h1)
    · rw [mem_cls.1 ((t.2 ⟨(c v)⁻¹, h⟩).symm ⟨v, hv⟩).2,
        mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc v))]

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (the inverse map): `(P, (σ_ζ))` is sent to the
involution of `V` that is `P` on `𝒞_1`, `σ_ζ` on `𝒞_ζ` and `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}`; it is a
matching compatible with `c`. -/
noncomputable def assemble (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples c R) :
    CompMatching c :=
  ⟨⟨assembleFun c R t, fun v => ⟨(assembleFun_spec hR hc t v).1, (assembleFun_spec hR hc t v).2.1⟩⟩,
    fun v => (assembleFun_spec hR hc t v).2.2⟩

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (explicit form of the inverse): the matching
assembled from `(P, (σ_ζ))` is `P` on `𝒞_1`, `σ_ζ` on `𝒞_ζ` and `σ_ζ^{−1}` on `𝒞_{ζ^{−1}}`, for
every `ζ ∈ ℛ`. -/
theorem lemma63_iii_assemble_apply (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples c R) :
    (∀ (v : Fin (2 * k + 2)) (hv : v ∈ cls c 1), (assemble hR hc t).1.1 v = (t.1.1 ⟨v, hv⟩).1) ∧
    (∀ (ζ : F) (hζ : ζ ∈ R) (v : Fin (2 * k + 2)) (hv : v ∈ cls c ζ),
        (assemble hR hc t).1.1 v = (t.2 ⟨ζ, hζ⟩ ⟨v, hv⟩).1) ∧
    (∀ (ζ : F) (hζ : ζ ∈ R) (v : Fin (2 * k + 2)) (hv : v ∈ cls c ζ⁻¹),
        (assemble hR hc t).1.1 v = ((t.2 ⟨ζ, hζ⟩).symm ⟨v, hv⟩).1) :=
  ⟨fun _ hv => assembleFun_one t hv, fun _ hζ _ hv => assembleFun_rep hR t hζ hv,
    fun _ hζ _ hv => assembleFun_inv hR t hζ hv⟩

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (injectivity of the restriction): assembling the
restrictions of a compatible matching `J` gives back `J`. -/
theorem lemma63_iii_assemble_restrict (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ)
    (J : CompMatching c) : assemble hR hc (restrict c R J) = J := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change assembleFun c R (restrict c R J) v = J.1.1 v
  rcases hR.cases (hc v) with h | h | h
  · rw [assembleFun_one _ (mem_cls.2 h)]; rfl
  · rw [assembleFun_rep hR _ h (mem_cls.2 rfl)]; rfl
  · rw [assembleFun_inv hR _ h (mem_cls.2 (inv_inv _).symm)]; rfl

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md` (surjectivity of the restriction): the
restrictions of the matching assembled from `(P, (σ_ζ))` are `P` and the `σ_ζ`. -/
theorem lemma63_iii_restrict_assemble (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) (t : Tuples c R) :
    restrict c R (assemble hR hc t) = t := by
  obtain ⟨P, σ⟩ := t
  refine Prod.ext (PerfMatch.ext fun v => Subtype.ext ?_) (funext fun ζ => Equiv.ext fun v =>
    Subtype.ext ?_)
  · exact assembleFun_one (P, σ) v.2
  · exact assembleFun_rep hR (P, σ) ζ.2 v.2

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the restriction map
`J ↦ (J|_{𝒞_1}, (J|_{𝒞_ζ})_{ζ ∈ ℛ})` is a bijection from the matchings compatible with `c` onto
the tuples `(P, (σ_ζ)_{ζ∈ℛ})`. -/
theorem lemma63_iii_bijective (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) :
    Function.Bijective (restrict c R) :=
  ⟨Function.LeftInverse.injective (lemma63_iii_assemble_restrict hR hc),
    Function.RightInverse.surjective (lemma63_iii_restrict_assemble hR hc)⟩

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: the bijection between compatible matchings and
tuples `(P, (σ_ζ))`, given by restriction, with inverse the assembly map. -/
noncomputable def compEquiv (hR : IsReps S R) (hc : ∀ v, c v ∈ S.μ) : CompMatching c ≃ Tuples c R where
  toFun := restrict c R
  invFun := assemble hR hc
  left_inv := lemma63_iii_assemble_restrict hR hc
  right_inv := lemma63_iii_restrict_assemble hR hc

end ColComp

end
