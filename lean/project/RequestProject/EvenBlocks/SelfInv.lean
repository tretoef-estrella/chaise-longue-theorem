module

public import RequestProject.EvenBlocks.Part0

/-!
# Part A of `q_even_blocks.md`: self-inverse colours, (A1)–(A7)

* `EvenBlocks.SInv S`: the self-inverse colours `{ζ ∈ μ : ζ^{−1} = ζ}`;
* `EvenBlocks.IsReps2 S R`: `R ⊆ μ ∖ SInv S` contains exactly one of `ζ, ζ^{−1}` for every
  `ζ ∈ μ ∖ SInv S`;
* (A1) `one_mem_SInv`, `mem_SInv_iff`, `SInv_subset`;
* (A2) `SInv_eq_singleton`, `even_r_facts`;
* (A3) `exists_isReps2`; (A4) `isReps2_iff_isReps`;
* (A5) `partitionA5`; (A6) `pair_iff`; (A7) `compatible_iff`.

No hypothesis on the parity of `p` or `r` is made anywhere.
-/

@[expose] public section

namespace EvenBlocks

open ColSplit ColSurv ColComp

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Part A, Definitions** of `q_even_blocks.md`: the self-inverse colours
`SInv S := {ζ ∈ μ : ζ^{−1} = ζ}`. -/
noncomputable def SInv : Finset F := S.μ.filter (fun ζ => ζ⁻¹ = ζ)

/-- **Part A, Definitions** of `q_even_blocks.md`: `R` is a set of representatives of the
non-self-inverse colours: `R ⊆ μ ∖ SInv S` and, for every `ζ ∈ μ ∖ SInv S`, exactly one of
`ζ, ζ^{−1}` lies in `R`. -/
def IsReps2 (R : Finset F) : Prop :=
  R ⊆ S.μ \ SInv S ∧ ∀ ζ ∈ S.μ \ SInv S, Xor' (ζ ∈ R) (ζ⁻¹ ∈ R)

variable {S}

/-- **Part A, (A1)** of `q_even_blocks.md`: `1 ∈ SInv S`. -/
theorem one_mem_SInv : (1 : F) ∈ SInv S := by
  simp [SInv, Setting.one_mem_μ S]

/-- **Part A, (A1)** of `q_even_blocks.md`: `ζ ∈ SInv S ↔ ζ ∈ μ ∧ ζ^2 = 1`. -/
theorem mem_SInv_iff {ζ : F} : ζ ∈ SInv S ↔ ζ ∈ S.μ ∧ ζ ^ 2 = 1 := by
  simp only [SInv, Finset.mem_filter]
  refine and_congr_right fun hζ => ?_
  have h0 : ζ ≠ 0 := Setting.ne_zero_of_mem_μ S hζ
  constructor
  · intro h
    rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel₀ h0
  · intro h
    rw [sq] at h
    exact (eq_inv_of_mul_eq_one_left h).symm

/-- **Part A, (A1)** of `q_even_blocks.md`: a self-inverse colour is its own inverse. -/
theorem inv_eq_of_mem_SInv {ζ : F} (h : ζ ∈ SInv S) : ζ⁻¹ = ζ :=
  (Finset.mem_filter.1 h).2

/-- **Part A, (A1)** of `q_even_blocks.md`: `SInv S ⊆ {1, −1}`. -/
theorem SInv_subset : SInv S ⊆ {1, -1} := by
  intro ζ hζ
  have h := (mem_SInv_iff.1 hζ).2
  rw [sq, mul_self_eq_one_iff] at h
  simpa using h

/-- **Part A, (A2) (a)** of `q_even_blocks.md`: if `r` is odd or `p = 2`, then `SInv S = {1}`. -/
theorem SInv_eq_singleton (h : Odd S.r ∨ S.p = 2) : SInv S = {1} := by
  apply le_antisymm _ (Finset.singleton_subset_iff.2 one_mem_SInv)
  intro ζ hζ
  rw [Finset.mem_singleton]
  rcases h with hr | hp
  · exact lemma63_i_self_inv hr (Finset.mem_filter.1 hζ).1 (inv_eq_of_mem_SInv hζ)
  · haveI := S.charP
    have h2 : (2 : F) = 0 := by
      have := (CharP.cast_eq_zero_iff F S.p 2).2 (by rw [hp])
      exact_mod_cast this
    have := SInv_subset hζ
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact h
    · rw [h]; linear_combination -h2

/-- **Part A, (A2) (b)** of `q_even_blocks.md`: if `r` is even, then `p ≠ 2`, `−1 ≠ 1` in `F`,
`−1 ∈ μ` and `SInv S = {1, −1}`. -/
theorem even_r_facts (h : Even S.r) :
    S.p ≠ 2 ∧ (-1 : F) ≠ 1 ∧ (-1 : F) ∈ S.μ ∧ SInv S = {1, -1} := by
  haveI := S.charP
  have hp2 : S.p ≠ 2 := by
    intro hp
    exact not_p_dvd_r S (hp ▸ even_iff_two_dvd.1 h)
  have hne : (-1 : F) ≠ 1 := by
    intro e
    have h2 : ((2 : ℕ) : F) = 0 := by push_cast; linear_combination -e
    rw [CharP.cast_eq_zero_iff F S.p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 h2)
  have hmem : (-1 : F) ∈ S.μ := (Setting.mem_μ_iff S _).2 h.neg_one_pow
  refine ⟨hp2, hne, hmem, le_antisymm SInv_subset ?_⟩
  intro ζ hζ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl
  · exact one_mem_SInv
  · exact mem_SInv_iff.2 ⟨hmem, by norm_num⟩

/-- **Part A, (A1)–(A3)** of `q_even_blocks.md` (proof): a colour of `μ ∖ SInv S` has its inverse
in `μ ∖ SInv S`, distinct from it. -/
theorem inv_mem_sdiff {ζ : F} (hζ : ζ ∈ S.μ \ SInv S) :
    ζ⁻¹ ∈ S.μ \ SInv S ∧ ζ⁻¹ ≠ ζ := by
  rw [Finset.mem_sdiff] at hζ ⊢
  have hne : ζ⁻¹ ≠ ζ := fun h => hζ.2 (Finset.mem_filter.2 ⟨hζ.1, h⟩)
  refine ⟨⟨Setting.inv_mem_μ S hζ.1, fun h => ?_⟩, hne⟩
  have := inv_eq_of_mem_SInv h
  rw [inv_inv] at this
  exact hne this.symm

/-- **Part A, (A3)** of `q_even_blocks.md`: for every Setting (every `r`, every `p`) there is a set
`R` of representatives, `IsReps2 S R`. -/
theorem exists_isReps2 : ∃ R : Finset F, IsReps2 S R := by
  refine ⟨(S.μ \ SInv S).filter fun ζ => WellOrderingRel ζ ζ⁻¹, Finset.filter_subset _ _, ?_⟩
  intro ζ hζ
  obtain ⟨hinv, hne⟩ := inv_mem_sdiff hζ
  simp only [Finset.mem_filter, hζ, hinv, true_and, inv_inv]
  rcases trichotomous_of WellOrderingRel ζ ζ⁻¹ with h | h | h
  · exact Or.inl ⟨h, fun h' => asymm h h'⟩
  · exact absurd h.symm hne
  · exact Or.inr ⟨h, fun h' => asymm h h'⟩

/-- **Part A, (A4)** of `q_even_blocks.md`: if `SInv S = {1}`, then `IsReps2 S R` is exactly
`ColComp.IsReps S R`. -/
theorem isReps2_iff_isReps (h : SInv S = {1}) (R : Finset F) : IsReps2 S R ↔ IsReps S R := by
  unfold IsReps2 IsReps
  rw [h, Finset.sdiff_singleton_eq_erase]

/-- **Part A** of `q_even_blocks.md` (proof of (A5)–(A8)): a representative `ζ ∈ R` lies in `μ`,
is not self-inverse, its inverse is not self-inverse, and `ζ^{−1} ∉ R`. -/
theorem IsReps2.mem {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R) :
    ζ ∈ S.μ ∧ ζ ∉ SInv S ∧ ζ⁻¹ ∉ SInv S ∧ ζ⁻¹ ∉ R ∧ ζ⁻¹ ≠ ζ := by
  have h := hR.1 hζ
  obtain ⟨hinv, hne⟩ := inv_mem_sdiff h
  rw [Finset.mem_sdiff] at h hinv
  exact ⟨h.1, h.2, hinv.2, fun h' => ((hR.2 ζ (Finset.mem_sdiff.2 h)).imp (fun h => h.2 h')
    (fun h => h.2 hζ)).elim id id, hne⟩

/-- **Part A** of `q_even_blocks.md` (proof of (A5)–(A8)): every colour `x ∈ μ` is self-inverse,
or lies in `R`, or has its inverse in `R`. -/
theorem IsReps2.cases {R : Finset F} (hR : IsReps2 S R) {x : F} (hx : x ∈ S.μ) :
    x ∈ SInv S ∨ x ∈ R ∨ x⁻¹ ∈ R := by
  by_cases h1 : x ∈ SInv S
  · exact Or.inl h1
  · right
    rcases hR.2 x (Finset.mem_sdiff.2 ⟨hx, h1⟩) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1

omit [Field F] in
/-- **Part A, (A5)** of `q_even_blocks.md` (proof): classes of distinct colours are disjoint. -/
theorem disjoint_cls (c : Fin (2 * k + 2) → F) {ζ η : F} (h : ζ ≠ η) :
    Disjoint (cls c ζ) (cls c η) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_cls] at hv hv'
  exact h (hv.symm.trans hv')

/-- **Part A, (A5)** of `q_even_blocks.md`: for a colouring `c : V → μ` and `IsReps2 S R`, the
classes `𝒞_ζ` (`ζ ∈ SInv S`) and the sets `𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ ∈ R`) are pairwise disjoint and
their union is `V`; moreover `𝒞_ζ` and `𝒞_{ζ^{−1}}` are disjoint for `ζ ∈ R`. -/
theorem partitionA5 {R : Finset F} (hR : IsReps2 S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) :
    (∀ ζ ∈ SInv S, ∀ η ∈ SInv S, ζ ≠ η → Disjoint (cls c ζ) (cls c η)) ∧
      (∀ ζ ∈ SInv S, ∀ η ∈ R, Disjoint (cls c ζ) (cls c η ∪ cls c η⁻¹)) ∧
      (∀ ζ ∈ R, Disjoint (cls c ζ) (cls c ζ⁻¹)) ∧
      (∀ ζ ∈ R, ∀ η ∈ R, ζ ≠ η → Disjoint (cls c ζ ∪ cls c ζ⁻¹) (cls c η ∪ cls c η⁻¹)) ∧
      (SInv S).biUnion (cls c) ∪ R.biUnion (fun ζ => cls c ζ ∪ cls c ζ⁻¹) = Finset.univ := by
  refine ⟨fun ζ _ η _ h => disjoint_cls c h, fun ζ hζ η hη => ?_,
    fun ζ hζ => disjoint_cls c (hR.mem hζ).2.2.2.2.symm, fun ζ hζ η hη hne => ?_, ?_⟩
  · have h := hR.mem hη
    refine Finset.disjoint_union_right.2 ⟨disjoint_cls c ?_, disjoint_cls c ?_⟩
    · rintro rfl; exact h.2.1 hζ
    · rintro rfl; exact h.2.2.1 hζ
  · rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, mem_cls] at hv hv'
    have a1 : ζ⁻¹ ∉ R := (hR.mem hζ).2.2.2.1
    have a2 : η⁻¹ ∉ R := (hR.mem hη).2.2.2.1
    rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;> rw [hv] at hv'
    · exact hne hv'
    · exact a2 (hv' ▸ hζ)
    · exact a1 (hv' ▸ hη)
    · exact hne (inv_injective hv')
  · rw [Finset.eq_univ_iff_forall]
    intro v
    simp only [Finset.mem_union, mem_cls, Finset.mem_biUnion]
    rcases hR.cases (hc v) with h | h | h
    · exact Or.inl ⟨c v, h, rfl⟩
    · exact Or.inr ⟨c v, h, Or.inl rfl⟩
    · exact Or.inr ⟨(c v)⁻¹, h, Or.inr (inv_inv _).symm⟩

/-- **Part A, (A6)** of `q_even_blocks.md`: for a colouring `c : V → μ` and `IsReps2 S R`,
`c_a c_b = 1` iff `a, b` lie in the same class `𝒞_ζ` of a self-inverse colour `ζ`, or there is
`ζ ∈ R` with one of `a, b` in `𝒞_ζ` and the other in `𝒞_{ζ^{−1}}`. -/
theorem pair_iff {R : Finset F} (hR : IsReps2 S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) (a b : Fin (2 * k + 2)) :
    c a * c b = 1 ↔ (∃ ζ ∈ SInv S, a ∈ cls c ζ ∧ b ∈ cls c ζ) ∨
      ∃ ζ ∈ R, (a ∈ cls c ζ ∧ b ∈ cls c ζ⁻¹) ∨ (b ∈ cls c ζ ∧ a ∈ cls c ζ⁻¹) := by
  simp only [mem_cls]
  constructor
  · intro h
    have hb : c b = (c a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rcases hR.cases (hc a) with h1 | h1 | h1
    · exact Or.inl ⟨c a, h1, rfl, by rw [hb, inv_eq_of_mem_SInv h1]⟩
    · exact Or.inr ⟨c a, h1, Or.inl ⟨rfl, hb⟩⟩
    · exact Or.inr ⟨(c a)⁻¹, h1, Or.inr ⟨hb, (inv_inv _).symm⟩⟩
  · rintro (⟨ζ, hζ, ha, hb⟩ | ⟨ζ, hζ, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩)
    · rw [ha, hb, ← sq]; exact (mem_SInv_iff.1 hζ).2
    · rw [ha, hb, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hR.mem hζ).1)]
    · rw [ha, hb, inv_mul_cancel₀ (Setting.ne_zero_of_mem_μ S (hR.mem hζ).1)]

/-- **Part A, (A7)** of `q_even_blocks.md`: for a colouring `c : V → μ` and `IsReps2 S R`, a
matching `J` is compatible with `c` iff `J(𝒞_ζ) = 𝒞_ζ` for every self-inverse colour `ζ` and
`J(𝒞_ζ) = 𝒞_{ζ^{−1}}` for every `ζ ∈ R`. -/
theorem compatible_iff {R : Finset F} (hR : IsReps2 S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) (J : BallotBound.Matching k) :
    Compatible c J ↔ (∀ ζ ∈ SInv S, (cls c ζ).image J.1 = cls c ζ) ∧
      ∀ ζ ∈ R, (cls c ζ).image J.1 = cls c ζ⁻¹ := by
  constructor
  · intro h
    refine ⟨fun ζ hζ => ?_, fun ζ _ => h.image_cls ζ⟩
    have := h.image_cls ζ
    rwa [inv_eq_of_mem_SInv hζ] at this
  · rintro ⟨h1, h2⟩ a
    rcases hR.cases (hc a) with ha | ha | ha
    · have : J.1 a ∈ cls c (c a) := h1 _ ha ▸ Finset.mem_image_of_mem _ (mem_cls.2 rfl)
      rw [mem_cls] at this
      rw [this, ← sq]; exact (mem_SInv_iff.1 ha).2
    · have : J.1 a ∈ cls c (c a)⁻¹ := h2 _ ha ▸ Finset.mem_image_of_mem _ (mem_cls.2 rfl)
      rw [mem_cls] at this
      rw [this, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc a))]
    · have hmem : a ∈ cls c (c a)⁻¹⁻¹ := mem_cls.2 (inv_inv _).symm
      rw [← h2 _ ha, Finset.mem_image] at hmem
      obtain ⟨b, hb, hba⟩ := hmem
      have : J.1 a = b := by rw [← hba, (J.2 b).2]
      rw [this, mem_cls.1 hb, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hc a))]

end EvenBlocks

end
