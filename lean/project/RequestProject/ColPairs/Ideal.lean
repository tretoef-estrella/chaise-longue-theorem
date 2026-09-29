module

public import RequestProject.ColPairs.Ring
public import RequestProject.ColPairs.Match

/-!
# The pair blocks: Lemma 6.7 (iii) and (iv) (`q_col_pairs.md`)

This file formalizes parts **(iii)** (identification) and **(iv)** (dimensions) of **Lemma 6.7**
of `q_col_pairs.md`, with the conventions of `RequestProject/ColPairs/Ring.lean`.

In (iii) the hypotheses `α = β = a`, `α = β + 1`, `β = α + 1` are expressed through the domains of
the enumerations: `e_A : [a] → A^*`, `e_B : [a] → B^*` (resp. `e_A : [β+1] → A^*`, `e_B : [β] → B^*`,
resp. `e_A : [α] → A^*`, `e_B : [α+1] → B^*`), which exist exactly under these hypotheses. The
isomorphism `Φ` (resp. `Φ'`) may be any `F`-algebra isomorphism with the values of Lemma 6.7 (i) on
the variables, e.g. `ColPairs.Phi` (resp. `ColPairs.Phi'`).
-/

@[expose] public section

open MvPolynomial

namespace ColPairs

open ColSplit ColSurv ColComp ColTensor ColDecomp

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-! ### Generalities -/

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md` (multiplying generators by units does not
change the ideal, as in Lemma 6.4 (v) of `q_col_tensor.md`): if every element of `E` is a unit
times an element of `E'`, and every element of `E'` is, up to a unit, an element of `E`, then
`(E) = (E')`. -/
theorem span_eq_of_units {A : Type*} [CommRing A] (E E' : Set A)
    (h1 : ∀ g ∈ E, ∃ g' ∈ E', ∃ u : Aˣ, g = u * g')
    (h2 : ∀ g' ∈ E', ∃ g ∈ E, ∃ u : Aˣ, g = u * g') : Ideal.span E = Ideal.span E' := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    obtain ⟨g', hg', u, rfl⟩ := h1 g hg
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg')
  · rw [Ideal.span_le]
    intro g' hg'
    obtain ⟨g, hg, u, hgu⟩ := h2 g' hg'
    have : g' = ((u⁻¹ : Aˣ) : A) * g := by rw [hgu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)

/-- **Proof** of Lemma 6.7 (iv) of `q_col_pairs.md`: an `F`-algebra isomorphism maps an ideal onto
its image ideal of the same dimension. -/
theorem finrank_map_algEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (Φ : A ≃ₐ[F] B) (I : Ideal A) :
    Module.finrank F (I.map Φ) = Module.finrank F (I.restrictScalars F) := by
  have h : (I.map Φ).restrictScalars F = (I.restrictScalars F).map Φ.toLinearMap := by
    ext y
    simp only [Submodule.restrictScalars_mem, Ideal.mem_map_of_equiv, Submodule.mem_map]
    rfl
  rw [← ((Submodule.restrictScalarsEquiv F B B (I.map Φ)).restrictScalars F).finrank_eq, h]
  exact ((I.restrictScalars F).equivMapOfInjective Φ.toLinearMap Φ.injective).finrank_eq.symm

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md` (case `0 ∈ A`): `(−1)^{q−1} = 1` in any
`F`-algebra, since `q − 1` is even if `p ≠ 2` and `−1 = 1` if `p = 2`. -/
theorem neg_one_pow_q_sub_one (S : ColSetting F) (A : Type*) [Ring A] [Algebra F A] :
    (-1 : A) ^ (S.q - 1) = 1 := by
  haveI := S.charP
  rcases S.hp.eq_two_or_odd' with h2 | hodd
  · have h : (2 : F) = 0 := by
      have := CharP.cast_eq_zero F S.p
      rw [h2] at this
      exact_mod_cast this
    have h' : (-1 : F) = 1 := by linear_combination -h
    have : (-1 : A) = 1 := by
      have := congrArg (algebraMap F A) h'
      simpa using this
    rw [this, one_pow]
  · have hq : Odd S.q := hodd.pow
    exact (Nat.Odd.sub_odd hq odd_one).neg_one_pow

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md` (case `0 ∈ A`): `(x − z)^{q−1} = (z − x)^{q−1}`. -/
theorem sub_pow_q_sub_one_comm (S : ColSetting F) {A : Type*} [CommRing A] [Algebra F A]
    (a b : A) : (a - b) ^ (S.q - 1) = (b - a) ^ (S.q - 1) := by
  rw [show a - b = (-1) * (b - a) by ring, mul_pow, neg_one_pow_q_sub_one S A, one_mul]

/-! ### The factors of `g_σ` -/

variable (S) in
/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`: the essential part of the factor of `g_σ` at
a pair `{a, b}` (`a ∈ A`, `b ∈ B`): `1` if the pair contains `0`, and `(x_a − z_b)^{q−1}`
otherwise. -/
noncomputable def pairTerm (c : Fin (2 * k + 1) → S.μ) (ζ : F) (a b : Fin (2 * k + 2)) :
    (boxS S c).Box (Wz S c ζ) :=
  if a = 0 ∨ b = 0 then 1 else (xW S c ζ a - zW S c ζ b) ^ (S.q - 1)

variable {R : Finset F} (hR : IsReps S R) {ζ : F} (hζ : ζ ∈ R) (c : Fin (2 * k + 1) → S.μ)

include hR hζ

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`: for `a ∈ A` and `b ∈ B`, the pair factor
`f_{min(a,b), max(a,b)}` is a unit times `pairTerm a b`: `f_{0,s} = t_s − 1` is a unit, and
`f_{i,l} = (t_b − 1)(t_i t_l − 1)^{q−1}` is a unit times `(x_i − z_l)^{q−1}` by (ii). -/
theorem pairF_eq_unit_mul {a b : Fin (2 * k + 2)} (ha : a ∈ cls (cExt c) ζ)
    (hb : b ∈ cls (cExt c) ζ⁻¹) :
    ∃ u : ((boxS S c).Box (Wz S c ζ))ˣ,
      pairF S.q (tB S c (Wz S c ζ)) (min a b) (max a b) = u * pairTerm S c ζ a b := by
  have hd := disjoint_AB hR hζ c
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hd ha (h ▸ hb)
  have memW : ∀ s, s ≠ 0 → (s ∈ cls (cExt c) ζ ∨ s ∈ cls (cExt c) ζ⁻¹) →
      s ∈ (cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹).erase 0 := fun s hs h =>
    Finset.mem_erase.2 ⟨hs, Finset.mem_union.2 h⟩
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := fun h => hab h.symm
    have hu := isUnit_tB_sub_one hR hζ c (memW b hb0 (Or.inr hb))
    refine ⟨hu.unit, ?_⟩
    rw [min_eq_left (Fin.zero_le b), max_eq_right (Fin.zero_le b), pairF, if_pos rfl, pairTerm,
      if_pos (Or.inl rfl), mul_one, IsUnit.unit_spec]
  by_cases hb0 : b = 0
  · subst hb0
    have hu := isUnit_tB_sub_one hR hζ c (memW a ha0 (Or.inl ha))
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
  obtain ⟨he, hu⟩ := (lemma67_ii hR hζ c).1 a (Finset.mem_erase.2 ⟨ha0, ha⟩) b
    (Finset.mem_erase.2 ⟨hb0, hb⟩)
  have hu1 := isUnit_tB_sub_one hR hζ c hmax
  refine ⟨hu1.unit * hu.unit ^ (S.q - 1), ?_⟩
  rw [pairF, if_neg hmin, hprod, he, pairTerm, if_neg (by tauto), Units.val_mul, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, IsUnit.unit_spec, mul_pow, mul_assoc]

/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`: `g_σ = (unit)·Π_{a ∈ A} pairTerm(a, σ(a))`,
i.e. `g_σ` is a unit times `Π (x_i − z_l)^{q−1}` over the pairs `{i, σ(i)}` avoiding `0`. -/
theorem gσ_eq_unit_mul (σ : cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹) :
    ∃ u : ((boxS S c).Box (Wz S c ζ))ˣ,
      gσ S c ζ σ = u * ∏ a : cls (cExt c) ζ, pairTerm S c ζ a.1 (σ a).1 := by
  choose u hu using fun a : cls (cExt c) ζ => pairF_eq_unit_mul hR hζ c a.2 (σ a).2
  refine ⟨∏ a, u a, ?_⟩
  rw [gσ, Units.coe_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => hu a

omit hR hζ in
/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`: an element of `A ∖ {0}` read in `A` when
`0 ∉ A` (and likewise for `B`). -/
def eraseZeroEquiv (T : Finset (Fin (2 * k + 2))) (h0 : (0 : Fin (2 * k + 2)) ∉ T) :
    (T.erase 0) ≃ T :=
  Equiv.subtypeEquivRight fun x => by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨fun hx => h0 (hx ▸ h), h⟩⟩

omit hR hζ in
/-- **Proof** of Lemma 6.7 (iii) of `q_col_pairs.md`: `T ∖ {0} ≅ {y ∈ T : y ≠ 0}` when `0 ∈ T`. -/
def eraseZeroEquivNe (T : Finset (Fin (2 * k + 2))) (h0 : (0 : Fin (2 * k + 2)) ∈ T) :
    (T.erase 0) ≃ {y : T // y ≠ ⟨0, h0⟩} where
  toFun x := ⟨⟨x.1, (Finset.mem_erase.1 x.2).2⟩,
    fun h => (Finset.mem_erase.1 x.2).1 (congrArg Subtype.val h)⟩
  invFun y := ⟨y.1.1, Finset.mem_erase.2 ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Lemma 6.7 (iii) -/

omit hR hζ in
/-- **Lemma 6.7 (iii)** of `q_col_pairs.md`, last case: if `|A| ≠ |B|` there is no bijection
`σ : A → B`, and `I_{c,ζ} = (∅) = 0`. -/
theorem lemma67_iii_ne (h : (cls (cExt c) ζ).card ≠ (cls (cExt c) ζ⁻¹).card) :
    Icz S c ζ = ⊥ := by
  have : IsEmpty (cls (cExt c) ζ ≃ cls (cExt c) ζ⁻¹) :=
    ⟨fun σ => h (by
      rw [← Fintype.card_coe, ← Fintype.card_coe (cls (cExt c) ζ⁻¹)]
      exact Fintype.card_congr σ)⟩
  rw [Icz, Set.range_eq_empty, Ideal.span_empty]

/-- **Lemma 6.7 (iii)** of `q_col_pairs.md`, first case: if `0 ∉ A ∪ B` and `α = β = a` (encoded by
the bijections `e_A : [a] → A^*`, `e_B : [a] → B^*`), then `Φ(I^{bal}_a) = I_{c,ζ}` (image ideal),
for any `F`-algebra isomorphism `Φ : R_{a,a} → B(W_ζ)` with `Φ(x_i) = x_{e_A(i)}` and
`Φ(z_l) = z_{e_B(l)}` (such as `ColPairs.Phi`). -/
theorem lemma67_iii_bal (h0 : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹) {a : ℕ}
    (eA : Fin a ≃ (cls (cExt c) ζ).erase 0) (eB : Fin a ≃ (cls (cExt c) ζ⁻¹).erase 0)
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
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ
    obtain ⟨τ, hτ⟩ := m1 σ
    exact ⟨_, ⟨τ, rfl⟩, u, by rw [hu, hpt, hτ, Function.comp_apply, hgen]⟩
  · rintro _ ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 τ
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ
    exact ⟨_, ⟨σ, rfl⟩, u, by rw [hu, hpt, hσ, Function.comp_apply, hgen]⟩

/-- **Lemma 6.7 (iii)** of `q_col_pairs.md`, second case: if `0 ∈ B` and `α = β + 1` (encoded by the
bijections `e_A : [β+1] → A^*`, `e_B : [β] → B^*`), then `Φ(I^{ph}_β) = I_{c,ζ}`, for any `F`-algebra
isomorphism `Φ : R_{β+1,β} → B(W_ζ)` with `Φ(x_i) = x_{e_A(i)}` and `Φ(z_l) = z_{e_B(l)}` (such as
`ColPairs.Phi`). -/
theorem lemma67_iii_ph (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ⁻¹) {m : ℕ}
    (eA : Fin (m + 1) ≃ (cls (cExt c) ζ).erase 0) (eB : Fin m ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ i, Φ (Bip.x F S.q i) = xW S c ζ (eA i))
    (hz : ∀ l, Φ (Bip.z F S.q l) = zW S c ζ (eB l)) :
    Ideal.map Φ (Bip.Iph F S.q m) = Icz S c ζ := by
  have h0A : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ := fun h =>
    Finset.disjoint_left.1 (disjoint_AB hR hζ c) h h0
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
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ
    obtain ⟨i₀, σ', hσ'⟩ := m1 σ
    exact ⟨_, ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩, u, by rw [hu, hpt, hσ', hgen]⟩
  · rintro _ ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 i₀ σ'
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ
    exact ⟨_, ⟨σ, rfl⟩, u, by rw [hu, hpt, hσ, hgen]⟩

/-- **Lemma 6.7 (iii)** of `q_col_pairs.md`, third case: if `0 ∈ A` and `β = α + 1` (encoded by the
bijections `e_A : [α] → A^*`, `e_B : [α+1] → B^*`), then `Φ'(I^{ph}_α) = I_{c,ζ}`, for any
`F`-algebra isomorphism `Φ' : R_{α+1,α} → B(W_ζ)` with `Φ'(x_l) = z_{e_B(l)}` and
`Φ'(z_i) = x_{e_A(i)}` (such as `ColPairs.Phi'`). -/
theorem lemma67_iii_ph' (h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ζ) {m : ℕ}
    (eA : Fin m ≃ (cls (cExt c) ζ).erase 0) (eB : Fin (m + 1) ≃ (cls (cExt c) ζ⁻¹).erase 0)
    (Φ' : Bip.R F S.q (m + 1) m ≃ₐ[F] (boxS S c).Box (Wz S c ζ))
    (hx : ∀ l, Φ' (Bip.x F S.q l) = zW S c ζ (eB l))
    (hz : ∀ i, Φ' (Bip.z F S.q i) = xW S c ζ (eA i)) :
    Ideal.map Φ' (Bip.Iph F S.q m) = Icz S c ζ := by
  have h0B : (0 : Fin (2 * k + 2)) ∉ cls (cExt c) ζ⁻¹ := fun h =>
    Finset.disjoint_left.1 (disjoint_AB hR hζ c) h0 h
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
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ
    obtain ⟨i₀, σ', hσ'⟩ := m1 σ.symm
    exact ⟨_, ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩, u, by rw [hu, hpt, hσ', hgen]⟩
  · rintro _ ⟨_, ⟨i₀, σ', rfl⟩, rfl⟩
    obtain ⟨σ, hσ⟩ := m2 i₀ σ'
    obtain ⟨u, hu⟩ := gσ_eq_unit_mul hR hζ c σ.symm
    refine ⟨_, ⟨σ.symm, rfl⟩, u, ?_⟩
    rw [hu, hpt, hgen, ← hσ]
    rfl

end ColPairs

end
