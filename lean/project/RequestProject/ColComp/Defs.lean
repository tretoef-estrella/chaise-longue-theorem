module

public import RequestProject.ColSurv.Defs

/-!
# Colour classes and compatible matchings: Setting, Lemma 6.3 (i) and (ii) (`q_col_compatible.md`)

This file formalizes the **Setting** of `q_col_compatible.md` and parts **(i)** and **(ii)** of
**Lemma 6.3**.

Conventions (reused from `q_col_splitting.md` and `q_col_survivors.md`):
* the data `F`, `p`, `q`, `r`, `μ` are bundled in `S : ColSplit.ColSetting F`; the extra
  hypothesis *"`r` is odd"* of the Setting is the hypothesis `Odd S.r`, added to exactly those
  statements whose proof needs it (the existence of representatives and the absence of
  self-inverse colours);
* `V = {0, 1, …, 2k+1}` is `Fin (2 * k + 2)`, a matching of `V` is a fixed-point-free involution
  `J : BallotBound.Matching k`;
* a colouring `c : V → μ` is a map `c : Fin (2 * k + 2) → F` together with the hypothesis
  `∀ v, c v ∈ S.μ` (the colouring `ColSurv.cExt c` of `q_col_survivors.md` is an example).
-/

@[expose] public section

namespace ColComp

open ColSplit ColSurv

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- **Colour classes** (**Setting** of `q_col_compatible.md`): for `ζ ∈ F`,
`𝒞_ζ := {v ∈ V : c_v = ζ}`. -/
noncomputable def cls (c : Fin (2 * k + 2) → F) (ζ : F) : Finset (Fin (2 * k + 2)) :=
  Finset.univ.filter fun v => c v = ζ

omit [Field F] in
/-- Membership in a colour class `𝒞_ζ` (**Setting** of `q_col_compatible.md`). -/
@[simp] theorem mem_cls {c : Fin (2 * k + 2) → F} {ζ : F} {v : Fin (2 * k + 2)} :
    v ∈ cls c ζ ↔ c v = ζ := by
  simp [cls]

/-- **Representatives** (**Setting** of `q_col_compatible.md`): a set `ℛ ⊆ μ ∖ {1}` containing
exactly one of `ζ, ζ^{−1}` for every `ζ ∈ μ ∖ {1}`. -/
def IsReps (R : Finset F) : Prop :=
  R ⊆ S.μ.erase 1 ∧ ∀ ζ ∈ S.μ.erase 1, Xor' (ζ ∈ R) (ζ⁻¹ ∈ R)

/-- **Compatibility** (**Setting** of `q_col_compatible.md`): a matching `J` of `V` is compatible
with `c` if `c_a c_{J(a)} = 1` for every `a ∈ V`. -/
def Compatible (c : Fin (2 * k + 2) → F) (J : BallotBound.Matching k) : Prop :=
  ∀ a, c a * c (J.1 a) = 1

variable {S}

/-- **Lemma 6.3 (i)** of `q_col_compatible.md` (no self-inverse colour): if `r` is odd, `ζ ∈ μ`
and `ζ^{−1} = ζ`, then `ζ = 1`. -/
theorem lemma63_i_self_inv (hr : Odd S.r) {ζ : F} (hζ : ζ ∈ S.μ) (h : ζ⁻¹ = ζ) : ζ = 1 := by
  have h0 : ζ ≠ 0 := Setting.ne_zero_of_mem_μ S hζ
  have hsq : ζ ^ 2 = 1 := by
    rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel₀ h0
  have hr' : ζ ^ S.r = 1 := (Setting.mem_μ_iff S ζ).1 hζ
  obtain ⟨t, ht⟩ := hr
  rw [ht, pow_succ, pow_mul, hsq, one_pow, one_mul] at hr'
  exact hr'

/-- **Lemma 6.3 (i)** of `q_col_compatible.md` (proof): an element of a set of representatives
is `≠ 1`, lies in `μ`, and its inverse is not a representative. -/
theorem IsReps.mem {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) :
    ζ ∈ S.μ ∧ ζ ≠ 1 ∧ ζ⁻¹ ∉ R := by
  have h := hR.1 hζ
  rw [Finset.mem_erase] at h
  exact ⟨h.2, h.1, fun h' => ((hR.2 ζ (Finset.mem_erase.2 h)).imp (fun h => h.2 h')
    (fun h => h.2 hζ)).elim id id⟩

/-- **Lemma 6.3 (i)** of `q_col_compatible.md` (proof): a representative is not its own inverse,
so `ζ ≠ ζ^{−1}` for `ζ ∈ ℛ`. -/
theorem IsReps.inv_ne {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) : ζ⁻¹ ≠ ζ := by
  intro h
  exact (hR.mem hζ).2.2 (by rw [h]; exact hζ)

/-- **Lemma 6.3 (i)** of `q_col_compatible.md` (proof): every colour `x ∈ μ` is `1`, or lies in
`ℛ`, or has its inverse in `ℛ`. -/
theorem IsReps.cases {R : Finset F} (hR : IsReps S R) {x : F} (hx : x ∈ S.μ) :
    x = 1 ∨ x ∈ R ∨ x⁻¹ ∈ R := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · right
    rcases hR.2 x (Finset.mem_erase.2 ⟨h1, hx⟩) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1

/-- **Lemma 6.3 (i)** of `q_col_compatible.md`: if `r` is odd, a set `ℛ` of representatives
exists. -/
theorem lemma63_i_exists_reps (hr : Odd S.r) : ∃ R : Finset F, IsReps S R := by
  classical
  refine ⟨(S.μ.erase 1).filter fun ζ => WellOrderingRel ζ ζ⁻¹, Finset.filter_subset _ _, ?_⟩
  intro ζ hζ
  have hζ' := Finset.mem_erase.1 hζ
  have hne : ζ⁻¹ ≠ ζ := fun h => hζ'.1 (lemma63_i_self_inv hr hζ'.2 h)
  have hinv : ζ⁻¹ ∈ S.μ.erase 1 :=
    Finset.mem_erase.2 ⟨fun h => hζ'.1 (inv_eq_one.1 h), Setting.inv_mem_μ S hζ'.2⟩
  simp only [Finset.mem_filter, hζ, hinv, true_and, inv_inv]
  rcases trichotomous_of WellOrderingRel ζ ζ⁻¹ with h | h | h
  · exact Or.inl ⟨h, fun h' => asymm h h'⟩
  · exact absurd h.symm hne
  · exact Or.inr ⟨h, fun h' => asymm h h'⟩

/-- **Lemma 6.3 (i)** of `q_col_compatible.md`: for `ζ ∈ ℛ`, the classes `𝒞_ζ`, `𝒞_{ζ^{−1}}` are
disjoint from each other and from `𝒞_1`. -/
theorem lemma63_i_disjoint {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R)
    (c : Fin (2 * k + 2) → F) :
    Disjoint (cls c ζ) (cls c ζ⁻¹) ∧ Disjoint (cls c ζ) (cls c 1) ∧
      Disjoint (cls c ζ⁻¹) (cls c 1) := by
  have h1 := (hR.mem hζ).2.1
  have h2 := hR.inv_ne hζ
  have h3 : ζ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.1 h)
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [mem_cls] at hv hv'
    rw [hv] at hv'
    first | exact h2 hv'.symm | exact h1 hv' | exact h3 hv'

/-- **Lemma 6.3 (i)** of `q_col_compatible.md`: for a colouring `c : V → μ`, the sets `𝒞_1` and
`𝒞_ζ ∪ 𝒞_{ζ^{−1}}` (`ζ ∈ ℛ`) partition `V`: they are pairwise disjoint and their union is `V`. -/
theorem lemma63_i_partition {R : Finset F} (hR : IsReps S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) :
    (∀ ζ ∈ R, Disjoint (cls c 1) (cls c ζ ∪ cls c ζ⁻¹)) ∧
      (∀ ζ ∈ R, ∀ η ∈ R, ζ ≠ η → Disjoint (cls c ζ ∪ cls c ζ⁻¹) (cls c η ∪ cls c η⁻¹)) ∧
      cls c 1 ∪ R.biUnion (fun ζ => cls c ζ ∪ cls c ζ⁻¹) = Finset.univ := by
  refine ⟨fun ζ hζ => ?_, fun ζ hζ η hη hne => ?_, ?_⟩
  · have h := lemma63_i_disjoint hR hζ c
    exact Finset.disjoint_union_right.2 ⟨h.2.1.symm, h.2.2.symm⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_union, mem_cls] at hv hv'
    have a1 : ζ⁻¹ ∉ R := (hR.mem hζ).2.2
    have a2 : η⁻¹ ∉ R := (hR.mem hη).2.2
    rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;> rw [hv] at hv'
    · exact hne hv'
    · exact a2 (hv' ▸ hζ)
    · exact a1 (hv' ▸ hη)
    · exact hne (inv_injective hv')
  · rw [Finset.eq_univ_iff_forall]
    intro v
    simp only [Finset.mem_union, mem_cls, Finset.mem_biUnion]
    rcases hR.cases (hc v) with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨c v, h, Or.inl rfl⟩
    · exact Or.inr ⟨(c v)⁻¹, h, Or.inr (inv_inv _).symm⟩

/-- **Lemma 6.3 (ii)** of `q_col_compatible.md` (compatible pairs): for a colouring `c : V → μ`,
`c_a c_b = 1` iff either `a, b ∈ 𝒞_1`, or there is `ζ ∈ ℛ` with one of `a, b` in `𝒞_ζ` and the other
in `𝒞_{ζ^{−1}}`.  (The file states this for `a ≠ b`; the equivalence holds for all `a, b`, so that
hypothesis is not needed.) -/
theorem lemma63_ii {R : Finset F} (hR : IsReps S R) {c : Fin (2 * k + 2) → F}
    (hc : ∀ v, c v ∈ S.μ) (a b : Fin (2 * k + 2)) :
    c a * c b = 1 ↔ (a ∈ cls c 1 ∧ b ∈ cls c 1) ∨
      ∃ ζ ∈ R, (a ∈ cls c ζ ∧ b ∈ cls c ζ⁻¹) ∨ (b ∈ cls c ζ ∧ a ∈ cls c ζ⁻¹) := by
  simp only [mem_cls]
  constructor
  · intro h
    have hb : c b = (c a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rcases hR.cases (hc a) with h1 | h1 | h1
    · exact Or.inl ⟨h1, by rw [hb, h1, inv_one]⟩
    · exact Or.inr ⟨c a, h1, Or.inl ⟨rfl, hb⟩⟩
    · exact Or.inr ⟨(c a)⁻¹, h1, Or.inr ⟨hb, (inv_inv _).symm⟩⟩
  · rintro (⟨ha, hb⟩ | ⟨ζ, hζ, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩)
    · rw [ha, hb, one_mul]
    · rw [ha, hb, mul_inv_cancel₀ (Setting.ne_zero_of_mem_μ S (hR.mem hζ).1)]
    · rw [ha, hb, inv_mul_cancel₀ (Setting.ne_zero_of_mem_μ S (hR.mem hζ).1)]

end ColComp

end
