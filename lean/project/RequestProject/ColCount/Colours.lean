module

public import RequestProject.ColCount.Defs

/-!
# Colours of a closed tuple (`q_col_count.md`, Proof of Lemma 6.8 (ii), first paragraph)

For a closed tuple `g ∈ T_m^n`, the colour multiset is closed under inversion, `|𝒞_1|` is even,
the colour product is `1`, and (for `n = 2k + 2`) some matching is compatible with the colour tuple.
-/

@[expose] public section

namespace ColCount

open ColSplit ColSurv ColComp Fibres TheoremB

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: the colour tuple
`κ(g) = (g_0.2, g_1.2, …)` of a tuple `g` of `T_m`. -/
noncomputable def col {n : ℕ} (g : Fin n → Tm S) (i : Fin n) : F := ((g i).1.2 : F)

/-- The colours of a tuple of `T_m` lie in `μ` (**Proof of Lemma 6.8 (ii)** of `q_col_count.md`). -/
theorem col_mem {n : ℕ} (g : Fin n → Tm S) (i : Fin n) : col g i ∈ S.μ := (g i).1.2.2

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*colours of a closed tuple*):
`cnt(κ(g), ζ) = cnt(κ(g), ζ^{−1})` for a closed tuple `g`. -/
theorem card_col_eq (hp : S.p ≠ 2) (hr : Odd S.r) {n : ℕ} {g : Fin n → Tm S}
    (hg : g ∈ closedTuples (TmSetting S hp hr) n) (ζ : F) :
    (Finset.univ.filter fun i => col g i = ζ).card =
      (Finset.univ.filter fun i => col g i = ζ⁻¹).card := by
  have hcl := (Finset.mem_filter.1 hg).2
  have e : ∀ ζ' : F, ∀ u ∈ Finset.univ.filter (fun u : Tm S => (u.1.2 : F) = ζ'),
      (Finset.univ.filter fun i => col g i = ζ').filter (fun i => g i = u) =
        Finset.univ.filter (fun i => g i = u) := by
    intro ζ' u hu
    rw [Finset.mem_filter] at hu
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    simp [col, h, hu.2]
  rw [Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : Tm S => (u.1.2 : F) = ζ)
      (by intro i hi; simpa [col] using hi),
    Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : Tm S => (u.1.2 : F) = ζ⁻¹)
      (by intro i hi; simpa [col] using hi),
    Finset.sum_congr rfl fun u hu => congrArg Finset.card (e ζ u hu),
    Finset.sum_congr rfl fun u hu => congrArg Finset.card (e ζ⁻¹ u hu)]
  refine Finset.sum_nbij' (negTm S) (negTm S) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    simp [negTm, invμ, hu]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    simp [negTm, invμ, hu]
  · intro u _
    exact (TmSetting S hp hr).neg_neg u
  · intro u _
    exact (TmSetting S hp hr).neg_neg u
  · intro u _
    exact hcl u

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md` (*colours of a closed tuple*): `|𝒞_1|` is even
for a closed tuple `g`. -/
theorem even_card_col_one (hp : S.p ≠ 2) (hr : Odd S.r) {n : ℕ} {g : Fin n → Tm S}
    (hg : g ∈ closedTuples (TmSetting S hp hr) n) :
    Even (Finset.univ.filter fun i => col g i = 1).card := by
  have hcl := (Finset.mem_filter.1 hg).2
  rw [Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : Tm S => (u.1.2 : F) = 1)
      (by intro i hi; simpa [col] using hi)]
  have e : ∀ u ∈ Finset.univ.filter (fun u : Tm S => (u.1.2 : F) = 1),
      (Finset.univ.filter fun i => col g i = 1).filter (fun i => g i = u) =
        Finset.univ.filter (fun i => g i = u) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    simp [col, h, hu.2]
  rw [Finset.sum_congr rfl fun u hu => congrArg Finset.card (e u hu), ← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_involution (fun u _ => negTm S u) ?_ ?_ ?_ ?_
  · intro u _
    have : (Finset.univ.filter fun i => g i = negTm S u).card =
        (Finset.univ.filter fun i => g i = u).card := (hcl u).symm
    rw [this, ← two_mul]
    exact mul_eq_zero_of_left rfl _
  · intro u _ _
    exact (TmSetting S hp hr).neg_ne u
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    simp [negTm, invμ, hu]
  · intro u _
    exact (TmSetting S hp hr).neg_neg u

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: for a closed tuple `g ∈ T_m^{2k+2}`, some
matching is compatible with its colour tuple (Lemma 6.3 (iv)). -/
theorem exists_compatible_col (hp : S.p ≠ 2) (hr : Odd S.r) {R : Finset F} (hR : IsReps S R)
    {k : ℕ} {g : Fin (2 * k + 2) → Tm S}
    (hg : g ∈ closedTuples (TmSetting S hp hr) (2 * k + 2)) :
    ∃ J : BallotBound.Matching k, Compatible (col g) J := by
  rw [lemma63_iv_exists hR (col_mem g)]
  exact ⟨even_card_col_one hp hr hg, fun ζ _ => card_col_eq hp hr hg ζ⟩

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: the colour product of a closed tuple
`g ∈ T_m^{2k+2}` is `1`. -/
theorem prod_col_eq_one (hp : S.p ≠ 2) (hr : Odd S.r) {R : Finset F} (hR : IsReps S R)
    {k : ℕ} {g : Fin (2 * k + 2) → Tm S}
    (hg : g ∈ closedTuples (TmSetting S hp hr) (2 * k + 2)) :
    ∏ i, col g i = 1 := by
  obtain ⟨J, hJ⟩ := exists_compatible_col hp hr hR hg
  have hbij : Function.Bijective J.1 := Function.Involutive.bijective fun x => (J.2 x).2
  have h2 : (∏ i, col g i) * ∏ i, col g i = 1 := by
    conv_lhs => arg 2; rw [← Fintype.prod_bijective J.1 hbij (fun i => col g (J.1 i)) (col g)
      (fun _ => rfl)]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => hJ a
  exact lemma63_i_self_inv hr (Setting.prod_mem_μ S _ _ fun i _ => col_mem g i)
    (inv_eq_of_mul_eq_one_right h2)

/-- **Proof of Lemma 6.8 (ii)** of `q_col_count.md`: the colour tuple of a closed tuple
`g ∈ T_m^{2k+2}` is the extended colouring of `c := (κ(g)_1, …, κ(g)_d)`. -/
theorem col_eq_cExt (hp : S.p ≠ 2) (hr : Odd S.r) {R : Finset F} (hR : IsReps S R)
    {k : ℕ} {g : Fin (2 * k + 2) → Tm S}
    (hg : g ∈ closedTuples (TmSetting S hp hr) (2 * k + 2)) :
    col g = cExt (fun j => (g j.succ).1.2) := by
  have hP := prod_col_eq_one hp hr hR hg
  rw [Fin.prod_univ_succ] at hP
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [cExt, Fin.cases_zero, c0]
    exact eq_inv_of_mul_eq_one_left hP
  | succ j => simp [cExt, col]

end ColCount

end
