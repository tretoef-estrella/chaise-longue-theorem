module

public import RequestProject.EvenColours.Points

/-!
# (C1) of `q_even_count_colours.md`: the colour of the index `0` is determined

* `EvenColours.C1_prod`: the colour product of a tuple of `closedT negT n` is `1`;
* `EvenColours.C1`: for `g ∈ closedT negT (2k+2)`, the colour of `g 0` is
  `cExt (fun j => (g j.succ).1.2) 0`;
* `EvenColours.exists_compatible`: the colour tuple of a closed tuple admits a compatible matching
  (used for (C2)).
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

/-- **(C1)** of `q_even_count_colours.md` (proof): a product over the entries of a tuple is the
product over the points `u` of the factor of `u` raised to `cnt g u`. -/
theorem prod_pow_cnt {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (g : Fin n → X)
    (φ : X → F) : ∏ i, φ (g i) = ∏ u, φ u ^ cnt g u := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := g) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  rfl

/-- **(C1)** of `q_even_count_colours.md`, first claim: for `g ∈ closedT negT n`,
`∏ i, ((g i).1.2 : F) = 1`. (The points `u` and `negT u` occur equally often and have inverse
colours; a fixed point has a colour `ζ` with `ζ^2 = 1` and occurs an even number of times.) -/
theorem C1_prod {n : ℕ} {g : Fin n → T2 S} (hg : g ∈ closedT (negT S) n) :
    ∏ i, ((g i).1.2 : F) = 1 := by
  have hcl := (Finset.mem_filter.1 hg).2
  rw [prod_pow_cnt g (fun u => ((u.1.2 : F)))]
  refine Finset.prod_involution (fun u _ => negT S u) ?_ ?_ (fun u _ => Finset.mem_univ _)
    (fun u _ => negT_negT S u)
  · intro u _
    have h0 : ((u.1.2 : F)) ≠ 0 := Setting.ne_zero_of_mem_μ S u.1.2.2
    show ((u.1.2 : F)) ^ cnt g u * ((u.1.2 : F))⁻¹ ^ cnt g (negT S u) = 1
    rw [← hcl.1 u, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ h0)]
  · intro u _ hne hfix
    apply hne
    have h0 : ((u.1.2 : F)) ≠ 0 := Setting.ne_zero_of_mem_μ S u.1.2.2
    obtain ⟨_, h2⟩ := (negT_eq_iff S u).1 hfix
    obtain ⟨t, ht⟩ := hcl.2 u hfix
    have hsq : ((u.1.2 : F)) ^ 2 = 1 := by
      rw [sq]; nth_rewrite 1 [← h2]; exact inv_mul_cancel₀ h0
    show ((u.1.2 : F)) ^ cnt g u = 1
    rw [ht, ← two_mul, pow_mul, hsq, one_pow]

/-- **(C1)** of `q_even_count_colours.md`, second claim: for `g ∈ closedT negT (2k+2)`,
`((g 0).1.2 : F) = cExt (fun j => (g j.succ).1.2) 0`. -/
theorem C1 {k : ℕ} {g : Fin (2 * k + 2) → T2 S} (hg : g ∈ closedT (negT S) (2 * k + 2)) :
    ((g 0).1.2 : F) = cExt (fun j => (g j.succ).1.2) 0 := by
  have hP := C1_prod hg
  rw [Fin.prod_univ_succ] at hP
  simp only [cExt, Fin.cases_zero, c0]
  exact eq_inv_of_mul_eq_one_left hP

/-- **(C1)** of `q_even_count_colours.md` (consequence): the colour tuple of
`g ∈ closedT negT (2k+2)` is the extended colouring of `c := ((g j.succ).1.2)_j`. -/
theorem col_eq_cExt {k : ℕ} {g : Fin (2 * k + 2) → T2 S}
    (hg : g ∈ closedT (negT S) (2 * k + 2)) (i : Fin (2 * k + 2)) :
    ((g i).1.2 : F) = cExt (fun j => (g j.succ).1.2) i := by
  cases i using Fin.cases with
  | zero => exact C1 hg
  | succ j => simp [cExt]

/-- **(C2)** of `q_even_count_colours.md` (proof): for `g ∈ closedT negT n`, the colours `ζ` and
`ζ^{−1}` occur equally often. -/
theorem card_col_eq {n : ℕ} {g : Fin n → T2 S} (hg : g ∈ closedT (negT S) n) (ζ : F) :
    (Finset.univ.filter fun i => ((g i).1.2 : F) = ζ).card =
      (Finset.univ.filter fun i => ((g i).1.2 : F) = ζ⁻¹).card := by
  have hcl := (Finset.mem_filter.1 hg).2.1
  have e : ∀ ζ' : F, ∀ u ∈ Finset.univ.filter (fun u : T2 S => (u.1.2 : F) = ζ'),
      (Finset.univ.filter fun i => ((g i).1.2 : F) = ζ').filter (fun i => g i = u) =
        Finset.univ.filter (fun i => g i = u) := by
    intro ζ' u hu
    rw [Finset.mem_filter] at hu
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    simp [h, hu.2]
  rw [Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : T2 S => (u.1.2 : F) = ζ)
      (by intro i hi; simpa using hi),
    Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : T2 S => (u.1.2 : F) = ζ⁻¹)
      (by intro i hi; simpa using hi),
    Finset.sum_congr rfl fun u hu => congrArg Finset.card (e ζ u hu),
    Finset.sum_congr rfl fun u hu => congrArg Finset.card (e ζ⁻¹ u hu)]
  refine Finset.sum_nbij' (negT S) (negT S) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨Finset.mem_univ _, by simp [negT, ColCount.invμ, hu.2]⟩
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨Finset.mem_univ _, by simp [negT, ColCount.invμ, hu.2]⟩
  · intro u _
    exact negT_negT S u
  · intro u _
    exact negT_negT S u
  · intro u _
    exact hcl u

/-- **(C2)** of `q_even_count_colours.md` (proof): for `g ∈ closedT negT n` and a self-inverse
colour `ζ` (`ζ^{−1} = ζ`), the colour `ζ` occurs an even number of times. -/
theorem even_card_col {n : ℕ} {g : Fin n → T2 S} (hg : g ∈ closedT (negT S) n) {ζ : F}
    (hζ : ζ⁻¹ = ζ) : Even (Finset.univ.filter fun i => ((g i).1.2 : F) = ζ).card := by
  have hsum : (Finset.univ.filter fun i => ((g i).1.2 : F) = ζ).card =
      ∑ u ∈ Finset.univ.filter (fun u : T2 S => (u.1.2 : F) = ζ), cnt g u := by
    rw [Finset.card_eq_sum_card_fiberwise (f := g)
      (t := Finset.univ.filter fun u : T2 S => (u.1.2 : F) = ζ)
      (by intro i hi; simpa using hi)]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold cnt
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (Finset.mem_filter.1 hu).2
  rw [hsum]
  refine even_sum_cnt (negT_negT S) hg _ fun u hu => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  simp [negT, ColCount.invμ, hu, hζ]

/-- **(C2)** of `q_even_count_colours.md` (proof: "a splitting matching is compatible with the
colours"): if `g ∈ closedT negT (2k+2)` has colour tuple `κ`, then some matching is compatible
with `κ` (by (A9) of `q_even_blocks.md`). -/
theorem exists_compatible {R : Finset F} (hR : IsReps2 S R) {k : ℕ}
    {g : Fin (2 * k + 2) → T2 S} (hg : g ∈ closedT (negT S) (2 * k + 2))
    {κ : Fin (2 * k + 2) → F} (hκ : ∀ i, ((g i).1.2 : F) = κ i) :
    ∃ J : BallotBound.Matching k, Compatible κ J := by
  have hκμ : ∀ i, κ i ∈ S.μ := fun i => hκ i ▸ (g i).1.2.2
  have hcls : ∀ ζ, cls κ ζ = Finset.univ.filter fun i => ((g i).1.2 : F) = ζ := by
    intro ζ
    ext i
    simp [cls, hκ i]
  rw [existsA9 hR hκμ]
  refine ⟨fun ζ hζ => ?_, fun ζ _ => ?_⟩
  · rw [hcls]
    exact even_card_col hg (inv_eq_of_mem_SInv hζ)
  · rw [hcls, hcls]
    exact card_col_eq hg ζ

end EvenColours

end
