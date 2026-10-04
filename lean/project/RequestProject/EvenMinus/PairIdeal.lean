module

public import RequestProject.EvenMinus.PairRing
public import RequestProject.BipAny.Main

/-!
# Part P of `q_even_block_minus.md`: Lemma 6.7 (iii), (iv), (vi) without `IsReps`, and Lemma 9.7

* (P1) `lemma67_iii_*_gen`, `lemma67_iv_gen` (under `ζ ≠ 0`, `ζ ≠ 1`, `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`) and
  `lemma67_iii_*_reps2`, `lemma67_iv_reps2` (under `IsReps2 S R`, `ζ ∈ R`). The last case of (iii),
  `ColPairs.lemma67_iii_ne`, has no hypothesis on `ζ` and applies as it stands.
* (P2) `lemma67_vi_gen`, `lemma67_vi_reps2`: Lemma 6.7 (vi) without `p ≠ 2`, using
  `BipAny.theoremC_prime_pow`.
* (P3) `lemma97_gen`, `lemma97`: Lemma 9.7, `Bip.Nbal |𝒞_ζ| q ≤ dim I_{c,ζ}` with the index `0`
  an ordinary coordinate.
-/

@[expose] public section

open MvPolynomial

namespace EvenMinus

open ColSplit ColSurv ColComp ColTensor ColDecomp ColPairs EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

section gen

variable {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (c : Fin (2 * k + 1) → S.μ)
  (hd : Disjoint (cls (cExt c) ζ) (cls (cExt c) ζ⁻¹))

include hζ0 hζ1 hd

/-- **Part P, (P1)** of `q_even_block_minus.md` (proof of Lemma 6.7 (iii), model
`ColPairs.pairF_eq_unit_mul`): for `a ∈ A`, `b ∈ B`, the pair factor `f_{min(a,b), max(a,b)}` is a
unit times `pairTerm a b`. -/
theorem pairF_eq_unit_mul_gen {a b : Fin (2 * k + 2)} (ha : a ∈ cls (cExt c) ζ)
    (hb : b ∈ cls (cExt c) ζ⁻¹) :
    ∃ u : ((boxS S c).Box (Wz S c ζ))ˣ,
      pairF S.q (tB S c (Wz S c ζ)) (min a b) (max a b) = u * pairTerm S c ζ a b := by
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hd ha (h ▸ hb)
  have memW : ∀ s, s ≠ 0 → (s ∈ cls (cExt c) ζ ∨ s ∈ cls (cExt c) ζ⁻¹) →
      s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0 := fun s hs h =>
    Finset.mem_erase.2 ⟨hs, Finset.mem_union.2 h⟩
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := fun h => hab h.symm
    have hu := isUnit_tB_sub_one_gen hζ1 c (memW b hb0 (Or.inr hb))
    refine ⟨hu.unit, ?_⟩
    rw [min_eq_left (Fin.zero_le b), max_eq_right (Fin.zero_le b), pairF, if_pos rfl, pairTerm,
      if_pos (Or.inl rfl), mul_one, IsUnit.unit_spec]
  by_cases hb0 : b = 0
  · subst hb0
    have hu := isUnit_tB_sub_one_gen hζ1 c (memW a ha0 (Or.inl ha))
    refine ⟨hu.unit, ?_⟩
    rw [min_eq_right (Fin.zero_le a), max_eq_left (Fin.zero_le a), pairF, if_pos rfl, pairTerm,
      if_pos (Or.inr rfl), mul_one, IsUnit.unit_spec]
  have hmin : min a b ≠ 0 := by rcases min_choice a b with h | h <;> rw [h] <;> assumption
  have hmax : max a b ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact memW a ha0 (Or.inl ha)
    · exact memW b hb0 (Or.inr hb)
  have hprod : tB S c (Wz S c ζ) (min a b) * tB S c (Wz S c ζ) (max a b) =
      tB S c (Wz S c ζ) a * tB S c (Wz S c ζ) b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact mul_comm _ _
  obtain ⟨he, hu⟩ := (lemma67_ii_gen hζ0 hζ1 c).1 a (Finset.mem_erase.2 ⟨ha0, ha⟩) b
    (Finset.mem_erase.2 ⟨hb0, hb⟩)
  have hu1 := isUnit_tB_sub_one_gen hζ1 c hmax
  refine ⟨hu1.unit * hu.unit ^ (S.q - 1), ?_⟩
  rw [pairF, if_neg hmin, hprod, he, pairTerm, if_neg (by tauto), Units.val_mul,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, IsUnit.unit_spec, mul_pow, mul_assoc]

/-- **Part P, (P1)** of `q_even_block_minus.md` (proof of Lemma 6.7 (iii), model
`ColPairs.gσ_eq_unit_mul`): `g_σ = (unit)·Π_{a ∈ A} pairTerm(a, σ(a))`. -/
theorem gσ_eq_unit_mul_gen (σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹) :
    ∃ u : ((boxS S c).Box (Wz S c ζ))ˣ,
      gσ S c ζ σ = u * ∏ a : cls (cExt c) ζ, pairTerm S c ζ a.1 (σ a).1 := by
  choose u hu using fun a : cls (cExt c) ζ => pairF_eq_unit_mul_gen hζ0 hζ1 c hd a.2 (σ a).2
  refine ⟨∏ a, u a, ?_⟩
  rw [gσ, Units.coe_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => hu a

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, first case
(`ColPairs.lemma67_iii_bal`), under `ζ ≠ 0`, `ζ ≠ 1` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`: if `0 ∉ A ∪ B` and
`α = β = a`, then `Φ(I^{bal}_a) = I_{c,ζ}` for every `F`-algebra isomorphism `Φ` with the values of
Lemma 6.7 (i). -/
theorem lemma67_iii_bal_gen (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹)
    {a : ℕ} (eA : Fin a ≃ (cls (cExt c) ζ).erase 0) (eB : Fin a ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ : Bip.R F S.q a a ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ i, Φ (Bip.x F S.q i) = xW S c ζ (eA i))
    (hz : ∀ l, Φ (Bip.z F S.q l) = zW S c ζ (eB l)) :
    Ideal.map Φ (Bip.Ibal F S.q a) = Icz S c ζ := by
  have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h => h0 (Finset.mem_union_left _ h)
  have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ := fun h => h0 (Finset.mem_union_right _ h)
  set eA' := eA.trans (eraseZeroEquiv _ h0A)
  set eB' := eB.trans (eraseZeroEquiv _ h0B)
  set f : cls (cExt c) ζ → cls (cExt c) ζ⁻¹ → (boxS S c).Box (Wz S c ζ) :=
    fun x y => (xW S c ζ x.1 - zW S c ζ y.1) ^ (S.q - 1)
  have hpt : ∀ σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹,
      ∏ a, pairTerm S c ζ a.1 (σ a).1 = ∏ a, f a (σ a) := fun σ =>
    Finset.prod_congr rfl fun a _ => by
      rw [pairTerm, if_neg]
      rintro (h | h)
      · exact h0A (h ▸ a.2)
      · exact h0B (h ▸ (σ a).2)
  have hgen : ∀ τ : Equiv.Perm (Fin a),
      Φ (∏ i : Fin a, (Bip.x F S.q i - Bip.z F S.q (τ i)) ^ (S.q - 1)) =
        ∏ i, f (eA' i) (eB' (τ i)) := fun τ => by
    simp only [map_prod, map_pow, map_sub, hx, hz]
    rfl
  obtain ⟨m1, m2⟩ := match_bal eA' eB' f
  rw [Bip.Ibal, Ideal.map_span, ← Set.range_comp, Icz]
  symm
  apply span_eq_of_units
  · rintro _ ⟨σ, rfl⟩
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ
    obtain ⟨τ, hτ⟩ := m1 σ
    exact ⟨_, ⟨τ, rfl⟩, u, by rw [hu, hpt, hτ, Function.comp_apply, hgen]⟩
  · rintro _ ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 τ
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ
    exact ⟨_, ⟨σ, rfl⟩, u, by rw [hu, hpt, hσ, Function.comp_apply, hgen]⟩

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, second case
(`ColPairs.lemma67_iii_ph`), under `ζ ≠ 0`, `ζ ≠ 1` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`: if `0 ∈ B` and
`α = β + 1`, then `Φ(I^{ph}_β) = I_{c,ζ}`. -/
theorem lemma67_iii_ph_gen (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹) {m : ℕ}
    (eA : Fin (m + 1) ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ i, Φ (Bip.x F S.q i) = xW S c ζ (eA i))
    (hz : ∀ l, Φ (Bip.z F S.q l) = zW S c ζ (eB l)) :
    Ideal.map Φ (Bip.Iph F S.q m) = Icz S c ζ := by
  have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 hd h h0
  set y0 : cls (cExt c) ζ⁻¹ := ⟨0, h0⟩
  set eA' := eA.trans (eraseZeroEquiv _ h0A)
  set eB' := eB.trans (eraseZeroEquivNe _ h0)
  set f : cls (cExt c) ζ → {y : cls (cExt c) ζ⁻¹ // y ≠ y0} → (boxS S c).Box (Wz S c ζ) :=
    fun x y => (xW S c ζ x.1 - zW S c ζ y.1.1) ^ (S.q - 1)
  have hpt : ∀ σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹,
      ∏ a, pairTerm S c ζ a.1 (σ a).1 =
        ∏ a, if h : σ a = y0 then 1 else f a ⟨σ a, h⟩ := fun σ =>
    Finset.prod_congr rfl fun a _ => by
      by_cases h : σ a = y0
      · rw [dif_pos h, pairTerm, if_pos (Or.inr (congrArg Subtype.val h))]
      · rw [dif_neg h, pairTerm, if_neg]
        rintro (h' | h')
        · exact h0A (h' ▸ a.2)
        · exact h (Subtype.ext h')
  have hgen : ∀ (i₀ : Fin (m + 1)) (σ' : {i // i ≠ i₀} ≃ Fin m),
      Φ (∏ i : {i // i ≠ i₀}, (Bip.x F S.q i.1 - Bip.z F S.q (σ' i)) ^ (S.q - 1)) =
        ∏ i : {i // i ≠ i₀}, f (eA' i) (eB' (σ' i)) := fun i₀ σ' => by
    simp only [map_prod, map_pow, map_sub, hx, hz]
    rfl
  obtain ⟨m1, m2⟩ := match_ph y0 eA' eB' f
  rw [Bip.Iph, Ideal.map_span, Icz]
  symm
  apply span_eq_of_units
  · rintro _ ⟨σ, rfl⟩
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ
    obtain ⟨i₀, σ', hσ'⟩ := m1 σ
    exact ⟨_, ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩, u, by rw [hu, hpt, hσ', hgen]⟩
  · rintro _ ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 i₀ σ'
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ
    exact ⟨_, ⟨σ, rfl⟩, u, by rw [hu, hpt, hσ, hgen]⟩

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, third case
(`ColPairs.lemma67_iii_ph'`), under `ζ ≠ 0`, `ζ ≠ 1` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`: if `0 ∈ A` and
`β = α + 1`, then `Φ'(I^{ph}_α) = I_{c,ζ}`. -/
theorem lemma67_iii_ph'_gen (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) {m : ℕ}
    (eA : Fin m ≃ (cls (cExt c) ζ).erase 0) (eB : Fin (m + 1) ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ' : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ l, Φ' (Bip.x F S.q l) = zW S c ζ (eB l))
    (hz : ∀ i, Φ' (Bip.z F S.q i) = xW S c ζ (eA i)) :
    Ideal.map Φ' (Bip.Iph F S.q m) = Icz S c ζ := by
  have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ := fun h =>
    Finset.disjoint_left.1 hd h0 h
  set y0 : cls (cExt c) ζ := ⟨0, h0⟩
  set eB' := eB.trans (eraseZeroEquiv _ h0B)
  set eA' := eA.trans (eraseZeroEquivNe _ h0)
  set f : cls (cExt c) ζ⁻¹ → {y : cls (cExt c) ζ // y ≠ y0} → (boxS S c).Box (Wz S c ζ) :=
    fun x y => (xW S c ζ y.1.1 - zW S c ζ x.1) ^ (S.q - 1)
  have hpt : ∀ σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹,
      ∏ a, pairTerm S c ζ a.1 (σ a).1 =
        ∏ b, if h : σ.symm b = y0 then 1 else f b ⟨σ.symm b, h⟩ := fun σ => by
    rw [← Equiv.prod_comp σ.symm (fun a : cls (cExt c) ζ => pairTerm S c ζ a.1 (σ a).1)]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Equiv.apply_symm_apply]
    by_cases h : σ.symm a = y0
    · rw [dif_pos h, pairTerm, if_pos (Or.inl (congrArg Subtype.val h))]
    · rw [dif_neg h, pairTerm, if_neg]
      rintro (h' | h')
      · exact h (Subtype.ext h')
      · exact h0B (h' ▸ a.2)
  have hgen : ∀ (i₀ : Fin (m + 1)) (σ' : {i // i ≠ i₀} ≃ Fin m),
      Φ' (∏ i : {i // i ≠ i₀}, (Bip.x F S.q i.1 - Bip.z F S.q (σ' i)) ^ (S.q - 1)) =
        ∏ i : {i // i ≠ i₀}, f (eB' i) (eA' (σ' i)) := fun i₀ σ' => by
    simp only [map_prod, map_pow, map_sub, hx, hz]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact sub_pow_q_sub_one_comm S _ _
  obtain ⟨m1, m2⟩ := match_ph y0 eB' eA' f
  rw [Bip.Iph, Ideal.map_span, Icz]
  symm
  apply span_eq_of_units
  · rintro _ ⟨σ, rfl⟩
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ
    obtain ⟨i₀, σ', hσ'⟩ := m1 σ.symm
    exact ⟨_, ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩, u, by rw [hu, hpt, hσ', hgen]⟩
  · rintro _ ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 i₀ σ'
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul_gen hζ0 hζ1 c hd σ.symm
    refine ⟨_, ⟨σ.symm, rfl⟩, u, ?_⟩
    rw [hu, hpt, hgen, ← hσ]
    rfl

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iv)** (`ColPairs.lemma67_iv`) under
`ζ ≠ 0`, `ζ ≠ 1` and `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`: in the three cases of (iii), `dim_F I_{c,ζ}` equals
`dim_F I^{bal}_a`, `dim_F I^{ph}_β`, `dim_F I^{ph}_α`; and if `|A| ≠ |B|` it is `0`. -/
theorem lemma67_iv_gen :
    (∀ a : ℕ, (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = a → ((cls (cExt c) ζ⁻¹).erase 0).card = a →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Ibal F S.q a).restrictScalars F)) ∧
    (∀ β : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = β + 1 → ((cls (cExt c) ζ⁻¹).erase 0).card = β →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q β).restrictScalars F)) ∧
    (∀ α : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ →
      ((cls (cExt c) ζ).erase 0).card = α → ((cls (cExt c) ζ⁻¹).erase 0).card = α + 1 →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q α).restrictScalars F)) ∧
    ((cls (cExt c) ζ).card ≠ (cls (cExt c) ζ⁻¹).card → Module.finrank F (Icz S c ζ) = 0) := by
  refine ⟨fun a h0 hα hβ => ?_, fun β h0 hα hβ => ?_, fun α h0 hα hβ => ?_, fun h => ?_⟩
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_bal_gen hζ0 hζ1 c hd h0 eA eB (PhiG hζ0 c hd eA eB) (PhiG_x hζ0 c hd eA eB)
      (PhiG_z hζ0 c hd eA eB), ColPairs.finrank_map_algEquiv]
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_ph_gen hζ0 hζ1 c hd h0 eA eB (PhiG hζ0 c hd eA eB) (PhiG_x hζ0 c hd eA eB)
      (PhiG_z hζ0 c hd eA eB), ColPairs.finrank_map_algEquiv]
  · set eA := (Finset.equivFinOfCardEq hα).symm
    set eB := (Finset.equivFinOfCardEq hβ).symm
    rw [← lemma67_iii_ph'_gen hζ0 hζ1 c hd h0 eA eB (PhiG' hζ0 c hd eA eB)
      (PhiG'_x hζ0 c hd eA eB) (PhiG'_z hζ0 c hd eA eB), ColPairs.finrank_map_algEquiv]
  · rw [lemma67_iii_ne c h]
    exact Module.finrank_zero_of_subsingleton

/-- **Part P, (P2)** of `q_even_block_minus.md`: **Lemma 6.7 (vi)** without `p ≠ 2`, for every
prime `p` (`2` included), under `ζ ≠ 0`, `ζ ≠ 1`, `𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅` and `|A| = |B|`: if
`0 ∉ A ∪ B`, `N_{bal}(|A ∖ 0|, q) ≤ dim I_{c,ζ}`; otherwise
`N_{ph}(min(|A ∖ 0|, |B ∖ 0|), q) ≤ dim I_{c,ζ}`. The proof is that of `ColPairs.lemma67_vi`, with
`BipAny.theoremC_prime_pow` in place of `Bip.theoremC`. -/
theorem lemma67_vi_gen (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    ((0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nbal ((cls (cExt c) ζ).erase 0).card S.q ≤ Module.finrank F (Icz S c ζ)) ∧
    ((0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nph (min ((cls (cExt c) ζ).erase 0).card ((cls (cExt c) ζ⁻¹).erase 0).card) S.q ≤
        Module.finrank F (Icz S c ζ)) := by
  haveI := S.charP
  have hC := BipAny.theoremC_prime_pow F S.hp S.one_le_v (q := S.q) rfl
  obtain ⟨ivb, ivp, ivp', -⟩ := lemma67_iv_gen hζ0 hζ1 c hd
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h => h0 (Finset.mem_union_left _ h)
    have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ :=
      fun h => h0 (Finset.mem_union_right _ h)
    rw [ivb _ h0 rfl (by rw [Finset.erase_eq_of_notMem h0A, Finset.erase_eq_of_notMem h0B, hAB])]
    exact (hC _).1
  · rcases Finset.mem_union.1 h0 with h0A | h0B
    · have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ :=
        fun h => Finset.disjoint_left.1 hd h0A h
      have hA := Finset.card_erase_of_mem h0A
      have hApos : 0 < (cls (cExt c) ζ).card := Finset.card_pos.2 ⟨0, h0A⟩
      have hB : ((cls (cExt c) ζ⁻¹).erase 0).card = ((cls (cExt c) ζ).erase 0).card + 1 := by
        rw [Finset.erase_eq_of_notMem h0B, hA, ← hAB]; omega
      rw [hB, min_eq_left (Nat.le_succ _), ivp' _ h0A rfl hB]
      exact (hC _).2.1
    · have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ :=
        fun h => Finset.disjoint_left.1 hd h h0B
      have hB := Finset.card_erase_of_mem h0B
      have hBpos : 0 < (cls (cExt c) ζ⁻¹).card := Finset.card_pos.2 ⟨0, h0B⟩
      have hA : ((cls (cExt c) ζ).erase 0).card = ((cls (cExt c) ζ⁻¹).erase 0).card + 1 := by
        rw [Finset.erase_eq_of_notMem h0A, hB, hAB]; omega
      rw [hA, min_eq_right (Nat.le_succ _), ivp _ h0B hA rfl]
      exact (hC _).2.1

/-- **Part P, (P3)** of `q_even_block_minus.md`: **Lemma 9.7** under `ζ ≠ 0`, `ζ ≠ 1` and
`𝒞_ζ ∩ 𝒞_{ζ^{−1}} = ∅`, for every prime `p`: if `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`, then
`N_{bal}(|𝒞_ζ|, q) ≤ dim_F I_{c,ζ}` (the index `0` an ordinary coordinate; via
`Bip.lemma72_iii` as in `ColCount.Nbal_eq_Nz`). -/
theorem lemma97_gen (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    Bip.Nbal (cls (cExt c) ζ).card S.q ≤ Module.finrank F (Icz S c ζ) := by
  obtain ⟨hvi1, hvi2⟩ := lemma67_vi_gen hζ0 hζ1 c hd hAB
  by_cases h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹
  · have key := hvi2 h0
    rcases Finset.mem_union.1 h0 with h0 | h0
    · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ := Finset.disjoint_left.1 hd h0
      have hpos : 0 < (cls (cExt c) ζ).card := Finset.card_pos.2 ⟨_, h0⟩
      rwa [Finset.card_erase_of_mem h0, Finset.erase_eq_of_notMem h0', ← hAB,
        min_eq_left (Nat.sub_le _ _), Bip.lemma72_iii, Nat.sub_add_cancel hpos] at key
    · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ :=
        fun h' => Finset.disjoint_left.1 hd h' h0
      have hpos : 0 < (cls (cExt c) ζ⁻¹).card := Finset.card_pos.2 ⟨_, h0⟩
      rw [Finset.card_erase_of_mem h0, Finset.erase_eq_of_notMem h0', hAB,
        min_eq_right (Nat.sub_le _ _), Bip.lemma72_iii, Nat.sub_add_cancel hpos] at key
      rw [hAB]
      exact key
  · have h0' : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h' => h0 (Finset.mem_union_left _ h')
    have key := hvi1 h0
    rwa [Finset.erase_eq_of_notMem h0'] at key

end gen

section reps2

variable {R : Finset F} (hR : IsReps2 S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)

include hR hζ

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, first case
(`ColPairs.lemma67_iii_bal`), under `IsReps2 S R` and `ζ ∈ R`. -/
theorem lemma67_iii_bal_reps2
    (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹) {a : ℕ}
    (eA : Fin a ≃ (cls (cExt c) ζ).erase 0) (eB : Fin a ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ : Bip.R F S.q a a ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ i, Φ (Bip.x F S.q i) = xW S c ζ (eA i))
    (hz : ∀ l, Φ (Bip.z F S.q l) = zW S c ζ (eB l)) :
    Ideal.map Φ (Bip.Ibal F S.q a) = Icz S c ζ :=
  lemma67_iii_bal_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c) h0 eA eB Φ hx hz

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, second case
(`ColPairs.lemma67_iii_ph`), under `IsReps2 S R` and `ζ ∈ R`. -/
theorem lemma67_iii_ph_reps2 (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹) {m : ℕ}
    (eA : Fin (m + 1) ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ i, Φ (Bip.x F S.q i) = xW S c ζ (eA i))
    (hz : ∀ l, Φ (Bip.z F S.q l) = zW S c ζ (eB l)) :
    Ideal.map Φ (Bip.Iph F S.q m) = Icz S c ζ :=
  lemma67_iii_ph_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c) h0 eA eB Φ hx hz

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, third case
(`ColPairs.lemma67_iii_ph'`), under `IsReps2 S R` and `ζ ∈ R`. -/
theorem lemma67_iii_ph'_reps2 (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) {m : ℕ}
    (eA : Fin m ≃ (cls (cExt c) ζ).erase 0) (eB : Fin (m + 1) ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ' : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ l, Φ' (Bip.x F S.q l) = zW S c ζ (eB l))
    (hz : ∀ i, Φ' (Bip.z F S.q i) = xW S c ζ (eA i)) :
    Ideal.map Φ' (Bip.Iph F S.q m) = Icz S c ζ :=
  lemma67_iii_ph'_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c) h0 eA eB Φ' hx hz

omit hR hζ in
/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iii)**, last case: if `|A| ≠ |B|`
then `I_{c,ζ} = 0`. This is `ColPairs.lemma67_iii_ne`, which has no hypothesis on `ζ` and is cited
unchanged. -/
theorem lemma67_iii_ne_reps2 (h : (cls (cExt c) ζ).card ≠ (cls (cExt c) ζ⁻¹).card) :
    Icz S c ζ = ⊥ :=
  lemma67_iii_ne c h

/-- **Part P, (P1)** of `q_even_block_minus.md`: **Lemma 6.7 (iv)** (`ColPairs.lemma67_iv`) under
`IsReps2 S R` and `ζ ∈ R`. -/
theorem lemma67_iv_reps2 :
    (∀ a : ℕ, (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = a → ((cls (cExt c) ζ⁻¹).erase 0).card = a →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Ibal F S.q a).restrictScalars F)) ∧
    (∀ β : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹ →
      ((cls (cExt c) ζ).erase 0).card = β + 1 → ((cls (cExt c) ζ⁻¹).erase 0).card = β →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q β).restrictScalars F)) ∧
    (∀ α : ℕ, (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ →
      ((cls (cExt c) ζ).erase 0).card = α → ((cls (cExt c) ζ⁻¹).erase 0).card = α + 1 →
      Module.finrank F (Icz S c ζ) = Module.finrank F ((Bip.Iph F S.q α).restrictScalars F)) ∧
    ((cls (cExt c) ζ).card ≠ (cls (cExt c) ζ⁻¹).card → Module.finrank F (Icz S c ζ) = 0) :=
  lemma67_iv_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c)

/-- **Part P, (P2)** of `q_even_block_minus.md`: **Lemma 6.7 (vi)** for every prime `p`
(`2` included; no hypothesis `p ≠ 2`), under `IsReps2 S R`, `ζ ∈ R` and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`. -/
theorem lemma67_vi_reps2 (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    ((0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nbal ((cls (cExt c) ζ).erase 0).card S.q ≤ Module.finrank F (Icz S c ζ)) ∧
    ((0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ →
      Bip.Nph (min ((cls (cExt c) ζ).erase 0).card ((cls (cExt c) ζ⁻¹).erase 0).card) S.q ≤
        Module.finrank F (Icz S c ζ)) :=
  lemma67_vi_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c) hAB

/-- **Part P, (P3)** of `q_even_block_minus.md`: **Lemma 9.7**. For every prime `p` (`2`
included), every `R` with `IsReps2 S R`, `ζ ∈ R` and `|𝒞_ζ| = |𝒞_{ζ^{−1}}|`:
`Bip.Nbal |𝒞_ζ| q ≤ dim_F I_{c,ζ}`, the index `0` being an ordinary coordinate. -/
theorem lemma97 (hAB : (cls (cExt c) ζ).card = (cls (cExt c) ζ⁻¹).card) :
    Bip.Nbal (cls (cExt c) ζ).card S.q ≤ Module.finrank F (Icz S c ζ) :=
  lemma97_gen (IsReps2.ne_zero hR hζ) (IsReps2.ne_one hR hζ) c (IsReps2.disjoint hR hζ c) hAB

end reps2

end EvenMinus

end
