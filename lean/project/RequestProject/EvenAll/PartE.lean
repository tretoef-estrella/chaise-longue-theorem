module

public import RequestProject.EvenAll.PartD

/-!
# Part E of `q_even_assembly.md`: Corollary 9.12 (ii) and Corollary 7.8, the bipartite ideals

* `EvenAll.colAB`: the colourings of (E1) (`A` coordinates of colour `ζ`, then `B` of colour
  `ζ⁻¹`, the rest of colour `1`).
* `EvenAll.bip_of_setting`: for every `ColSetting S` over a field `K` with a colour `ζ ∈ S.μ`,
  `ζ⁻¹ ≠ ζ`, and every `a`: `finrank (Ibal K S.q a) = Nbal a S.q` and
  `finrank (Iph K S.q a) = Nph a S.q`.
* **(E1)** `EvenAll.E1` (Corollary 9.12 (ii), `p = 2`) and **(E2)** `EvenAll.E2`
  (Corollary 7.8, odd `p`), both from `EvenAll.E_prime` (every prime `p`).
-/

@[expose] public section

namespace EvenAll

open ColSplit ColSurv ColComp ColDecomp EvenBlocks Finset

open scoped Classical

set_option synthInstance.maxHeartbeats 200000

variable {K : Type*} [Field K] (S : ColSetting K)

/-- **Part E, (E1)** of `q_even_assembly.md` (the colourings): for `ζ ∈ S.μ`, the colouring
`c : Fin (2k+1) → S.μ` with `c_j = ζ` for `j < A`, `c_j = ζ⁻¹` for `A ≤ j < A + B` and `c_j = 1`
otherwise. (For `Ibal`: `k = A = B = a`; for `Iph`: `k = a`, `A = a + 1`, `B = a`.) -/
noncomputable def colAB {ζ : K} (hζ : ζ ∈ S.μ) (k A B : ℕ) : Fin (2 * k + 1) → S.μ :=
  fun j => if j.val < A then ⟨ζ, hζ⟩
    else if j.val < A + B then ⟨ζ⁻¹, Setting.inv_mem_μ S hζ⟩ else ⟨1, Setting.one_mem_μ S⟩

variable {S}

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): the values of `colAB`. -/
theorem colAB_val {ζ : K} (hζ : ζ ∈ S.μ) (k A B : ℕ) (j : Fin (2 * k + 1)) :
    ((colAB S hζ k A B j : S.μ) : K) =
      if j.val < A then ζ else if j.val < A + B then ζ⁻¹ else 1 := by
  unfold colAB
  split_ifs <;> rfl

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): the number of `j ∈ Fin n` in the window
`A ≤ j < A + B` is `B` (if `A + B ≤ n`). -/
theorem card_window (n A B : ℕ) (h : A + B ≤ n) :
    (univ.filter fun i : Fin n => A ≤ i.val ∧ i.val < A + B).card = B := by
  have h1 := Fin.card_filter_val_lt (n := n) (m := A + B)
  have h2 := Fin.card_filter_val_lt (n := n) (m := A)
  have hu : (univ.filter fun i : Fin n => i.val < A + B) =
      (univ.filter fun i : Fin n => i.val < A) ∪
        (univ.filter fun i : Fin n => A ≤ i.val ∧ i.val < A + B) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
  have hd : Disjoint (univ.filter fun i : Fin n => i.val < A)
      (univ.filter fun i : Fin n => A ≤ i.val ∧ i.val < A + B) := by
    rw [disjoint_filter]; intro i _ h1 h2; omega
  rw [hu, card_union_of_disjoint hd] at h1
  omega

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): the number of coordinates of `colAB` of
colour `ξ` (the three colours `ζ`, `ζ⁻¹`, `1` are distinct). -/
theorem card_filter_colAB {ζ : K} (hζ : ζ ∈ S.μ) (hz1 : ζ ≠ 1) (hzi : ζ⁻¹ ≠ ζ) {k A B : ℕ}
    (hAB : A + B ≤ 2 * k + 1) (ξ : K) :
    (univ.filter fun j => ((colAB S hζ k A B j : S.μ) : K) = ξ).card =
      (if ξ = ζ then A else 0) + (if ξ = ζ⁻¹ then B else 0) +
        (if ξ = 1 then 2 * k + 1 - (A + B) else 0) := by
  have hi1 : ζ⁻¹ ≠ 1 := fun h => hz1 (inv_eq_one.1 h)
  simp_rw [colAB_val]
  by_cases h1 : ξ = ζ
  · subst h1
    rw [if_pos rfl, if_neg hzi.symm, if_neg hz1]
    have : (univ.filter fun j : Fin (2 * k + 1) =>
        (if j.val < A then ξ else if j.val < A + B then ξ⁻¹ else 1) = ξ) =
        univ.filter fun j : Fin (2 * k + 1) => 0 ≤ j.val ∧ j.val < 0 + A := by
      ext j; simp only [mem_filter, mem_univ, true_and]
      split_ifs with ha hb
      · simp only [true_iff]; omega
      · simp only [hzi, false_iff]; omega
      · simp only [hz1.symm, false_iff]; omega
    rw [this, card_window _ _ _ (by omega)]; rfl
  by_cases h2 : ξ = ζ⁻¹
  · subst h2
    rw [if_neg h1, if_pos rfl, if_neg hi1]
    have : (univ.filter fun j : Fin (2 * k + 1) =>
        (if j.val < A then ζ else if j.val < A + B then ζ⁻¹ else 1) = ζ⁻¹) =
        univ.filter fun j : Fin (2 * k + 1) => A ≤ j.val ∧ j.val < A + B := by
      ext j; simp only [mem_filter, mem_univ, true_and]
      split_ifs with ha hb
      · simp only [hzi.symm, false_iff]; omega
      · simp only [true_iff]; omega
      · simp only [hi1.symm, false_iff]; omega
    rw [this, card_window _ _ _ hAB]; simp
  by_cases h3 : ξ = 1
  · subst h3
    rw [if_neg h1, if_neg h2, if_pos rfl]
    have : (univ.filter fun j : Fin (2 * k + 1) =>
        (if j.val < A then ζ else if j.val < A + B then ζ⁻¹ else (1 : K)) = 1) =
        univ.filter fun j : Fin (2 * k + 1) =>
          A + B ≤ j.val ∧ j.val < A + B + (2 * k + 1 - (A + B)) := by
      ext j; simp only [mem_filter, mem_univ, true_and]
      split_ifs with ha hb
      · simp only [hz1, false_iff]; omega
      · simp only [hi1, false_iff]; omega
      · simp only [true_iff]; omega
    rw [this, card_window _ _ _ (by omega)]; simp
  · rw [if_neg h1, if_neg h2, if_neg h3]
    simp only [add_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies]
    intro j
    split_ifs
    · exact fun h => h1 h.symm
    · exact fun h => h2 h.symm
    · exact fun h => h3 h.symm

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): the product of the colours of
`colAB` is `ζ^A · (ζ⁻¹)^B`. -/
theorem prod_colAB {ζ : K} (hζ : ζ ∈ S.μ) {k A B : ℕ} (hAB : A + B ≤ 2 * k + 1) :
    ∏ j, ((colAB S hζ k A B j : S.μ) : K) = ζ ^ A * ζ⁻¹ ^ B := by
  simp_rw [colAB_val]
  rw [Finset.prod_ite, Finset.prod_ite, prod_const, prod_const, prod_const_one, mul_one,
    filter_filter, Fin.card_filter_val_lt, min_eq_right (by omega)]
  congr 2
  have := card_window (2 * k + 1) A B hAB
  rw [← this]
  congr 1
  ext j; simp only [mem_filter, mem_univ, true_and]; omega

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): the class sizes of a colouring, read off
`c_0` and the coordinates `1, …, 2k+1`. -/
theorem card_cls_cExt {k : ℕ} (c : Fin (2 * k + 1) → S.μ) (ξ : K) :
    (cls (cExt c) ξ).card = (if c0 c = ξ then 1 else 0) +
      (univ.filter fun j => ((c j : S.μ) : K) = ξ).card := by
  unfold cls
  rw [Fin.card_filter_univ_succ']
  rfl

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary): `0 ∈ 𝒞_ξ` iff `c_0 = ξ`. -/
theorem zero_mem_cls_cExt {k : ℕ} (c : Fin (2 * k + 1) → S.μ) (ξ : K) :
    (0 : Fin (2 * k + 2)) ∈ cls (cExt c) ξ ↔ c0 c = ξ := by
  rw [mem_cls]
  rfl

/-- **Part E, (E1)** of `q_even_assembly.md` (auxiliary; "a compatible matching exists by
`existsA9`"): if the class sizes of `c` are `|𝒞_ζ| = |𝒞_{ζ⁻¹}| = α`, `|𝒞_1| = β` even, and `0`
otherwise, then `c` has a compatible matching. -/
theorem compat_of_card {R : Finset K} (hR : IsReps2 S R) {ζ : K} (hζR : ζ ∈ R) {k : ℕ}
    (c : Fin (2 * k + 1) → S.μ) (α β : ℕ) (hβ : Even β)
    (hcard : ∀ ξ, (cls (cExt c) ξ).card =
      (if ξ = ζ then α else 0) + (if ξ = ζ⁻¹ then α else 0) + (if ξ = 1 then β else 0)) :
    ∃ J : BallotBound.Matching k, Compatible (cExt c) J := by
  have hζs := hR.1 hζR
  have hzi : ζ⁻¹ ≠ ζ := fun h => (mem_sdiff.1 hζs).2 (mem_filter.2 ⟨(mem_sdiff.1 hζs).1, h⟩)
  rw [existsA9 hR (cExt_mem c)]
  refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have hξi : ξ⁻¹ = ξ := (mem_filter.1 hξ).2
    have h1 : ξ ≠ ζ := fun h => hzi (h ▸ hξi)
    have h2 : ξ ≠ ζ⁻¹ := fun h => hzi (by rw [← h, ← hξi, h, inv_inv])
    rw [hcard, if_neg h1, if_neg h2]
    split_ifs
    · simpa using hβ
    · exact ⟨0, rfl⟩
  · have hξs := hR.1 hξ
    have hξ1 : ξ ≠ 1 := fun h => (mem_sdiff.1 hξs).2 (h ▸ one_mem_SInv)
    by_cases h : ξ = ζ
    · subst h
      rw [hcard, hcard, if_pos rfl, if_neg hzi.symm, if_neg hξ1, if_neg hzi, if_pos rfl,
        if_neg (fun h => hξ1 (inv_eq_one.1 h))]
      simp
    · have hξz : ξ ≠ ζ⁻¹ := by
        intro h'
        have hx := hR.2 ζ hζs
        rw [← h'] at hx
        exact (xor_iff_iff_not.1 hx).1 hζR hξ
      have hi1 : ξ⁻¹ ≠ ζ := fun h' => hξz (by rw [← h', inv_inv])
      have hi2 : ξ⁻¹ ≠ ζ⁻¹ := fun h' => h (inv_injective h')
      have hi3 : ξ⁻¹ ≠ 1 := fun h' => hξ1 (inv_eq_one.1 h')
      rw [hcard, hcard, if_neg h, if_neg hξz, if_neg hξ1, if_neg hi1, if_neg hi2, if_neg hi3]

/-- **Part E, (E1)** of `q_even_assembly.md` (the argument of (E1) for one setting, with `ζ ∈ R`):
for every `ColSetting S` over `K`, every `R` with `IsReps2 S R`, every `ζ ∈ R` and every `a`:
`finrank K (Ibal K S.q a) = Nbal a S.q` and `finrank K (Iph K S.q a) = Nph a S.q`. (For `Ibal`:
the colouring with `a` coordinates `ζ`, `a` coordinates `ζ⁻¹` and the last one `1`;
`EvenMinus.lemma67_iv_reps2` (first case) and (D2). For `Iph`: `a + 1` coordinates `ζ`, `a`
coordinates `ζ⁻¹`; `lemma67_iv_reps2` (second case, `β = a`), (D2) and `Bip.lemma72_iii`.) -/
theorem bip_of_reps {R : Finset K} (hR : IsReps2 S R) {ζ : K} (hζR : ζ ∈ R) (a : ℕ) :
    Module.finrank K ((Bip.Ibal K S.q a).restrictScalars K) = Bip.Nbal a S.q ∧
      Module.finrank K ((Bip.Iph K S.q a).restrictScalars K) = Bip.Nph a S.q := by
  have hζs := hR.1 hζR
  have hζ : ζ ∈ S.μ := (mem_sdiff.1 hζs).1
  have hzi : ζ⁻¹ ≠ ζ := fun h => (mem_sdiff.1 hζs).2 (mem_filter.2 ⟨hζ, h⟩)
  have hz1 : ζ ≠ 1 := fun h => hzi (by rw [h, inv_one])
  have hi1 : ζ⁻¹ ≠ 1 := fun h => hz1 (inv_eq_one.1 h)
  have hz0 : ζ ≠ 0 := Setting.ne_zero_of_mem_μ S hζ
  constructor
  · -- `Ibal`
    let c := colAB S hζ a a a
    have hc0 : c0 c = 1 := by
      unfold c0
      rw [prod_colAB hζ (by omega), inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz0), inv_one]
    have hcard : ∀ ξ, (cls (cExt c) ξ).card =
        (if ξ = ζ then a else 0) + (if ξ = ζ⁻¹ then a else 0) + (if ξ = 1 then 2 else 0) := by
      intro ξ
      rw [card_cls_cExt, card_filter_colAB hζ hz1 hzi (by omega), hc0]
      by_cases h : ξ = 1
      · subst h; simp [hz1.symm, hi1.symm]; omega
      · rw [if_neg (Ne.symm h), if_neg h, if_neg h]; ring
    have hcomp := compat_of_card hR hζR c a 2 even_two hcard
    have hcz : (cls (cExt c) ζ).card = a := by
      rw [hcard, if_pos rfl, if_neg hzi.symm, if_neg hz1]; rfl
    have hczi : (cls (cExt c) ζ⁻¹).card = a := by
      rw [hcard, if_neg hzi, if_pos rfl, if_neg hi1]; simp
    have h0 : (0 : Fin (2 * a + 2)) ∉ cls (cExt c) ζ ∪ cls (cExt c) ζ⁻¹ := by
      rw [mem_union, zero_mem_cls_cExt, zero_mem_cls_cExt, hc0]
      rintro (h | h)
      · exact hz1 h.symm
      · exact hi1 h.symm
    have h0z : (0 : Fin (2 * a + 2)) ∉ cls (cExt c) ζ := fun h => h0 (mem_union_left _ h)
    have h0zi : (0 : Fin (2 * a + 2)) ∉ cls (cExt c) ζ⁻¹ := fun h => h0 (mem_union_right _ h)
    have key := (EvenMinus.lemma67_iv_reps2 hR hζR c).1 a h0
      (by rw [erase_eq_of_notMem h0z, hcz]) (by rw [erase_eq_of_notMem h0zi, hczi])
    rw [← key, (D2 S hR c hcomp).2 ζ hζR, hcz]
  · -- `Iph`
    let c := colAB S hζ a (a + 1) a
    have hc0 : c0 c = ζ⁻¹ := by
      unfold c0
      rw [prod_colAB hζ (by omega), pow_succ, inv_pow, mul_comm (ζ ^ a * ζ),
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz0), one_mul]
    have hcard : ∀ ξ, (cls (cExt c) ξ).card =
        (if ξ = ζ then a + 1 else 0) + (if ξ = ζ⁻¹ then a + 1 else 0) + (if ξ = 1 then 0 else 0) := by
      intro ξ
      rw [card_cls_cExt, card_filter_colAB hζ hz1 hzi (by omega), hc0]
      by_cases h : ξ = ζ⁻¹
      · subst h; simp [hzi, hi1]; ring
      · simp only [if_neg (Ne.symm h), if_neg h]
        split_ifs <;> omega
    have hcomp := compat_of_card hR hζR c (a + 1) 0 ⟨0, rfl⟩ hcard
    have hcz : (cls (cExt c) ζ).card = a + 1 := by
      rw [hcard, if_pos rfl, if_neg hzi.symm, if_neg hz1]
    have hczi : (cls (cExt c) ζ⁻¹).card = a + 1 := by
      rw [hcard, if_neg hzi, if_pos rfl, if_neg hi1]; simp
    have h0zi : (0 : Fin (2 * a + 2)) ∈ cls (cExt c) ζ⁻¹ := by
      rw [zero_mem_cls_cExt, hc0]
    have h0z : (0 : Fin (2 * a + 2)) ∉ cls (cExt c) ζ := by
      rw [zero_mem_cls_cExt, hc0]; exact hzi
    have key := (EvenMinus.lemma67_iv_reps2 hR hζR c).2.1 a h0zi
      (by rw [erase_eq_of_notMem h0z, hcz]) (by rw [card_erase_of_mem h0zi, hczi]; rfl)
    rw [← key, (D2 S hR c hcomp).2 ζ hζR, hcz, Bip.lemma72_iii]

/-- **Part E, (E1)–(E2)** of `q_even_assembly.md` (general form): for every `ColSetting S` over a
field `K` that contains a colour `ζ ∈ S.μ` with `ζ⁻¹ ≠ ζ`, and every `a`:
`finrank K (Ibal K S.q a) = Nbal a S.q` and `finrank K (Iph K S.q a) = Nph a S.q`. (Take `R` with
`IsReps2 S R` (`exists_isReps2`); one of `ζ`, `ζ⁻¹` lies in `R`; apply `bip_of_reps`.)
**More general** than (E1), (E2): any such setting, over any field. -/
theorem bip_of_setting {ζ : K} (hζ : ζ ∈ S.μ) (hzi : ζ⁻¹ ≠ ζ) (a : ℕ) :
    Module.finrank K ((Bip.Ibal K S.q a).restrictScalars K) = Bip.Nbal a S.q ∧
      Module.finrank K ((Bip.Iph K S.q a).restrictScalars K) = Bip.Nph a S.q := by
  obtain ⟨R, hR⟩ := exists_isReps2 (S := S)
  have hζs : ζ ∈ S.μ \ SInv S := mem_sdiff.2 ⟨hζ, fun h => hzi (mem_filter.1 h).2⟩
  rcases hR.2 ζ hζs with ⟨h, -⟩ | ⟨h, -⟩
  · exact bip_of_reps hR h a
  · exact bip_of_reps hR h a

/-- **Part E** of `q_even_assembly.md` (auxiliary): over `AlgebraicClosure (ZMod p)`, for
`r ≥ 3` with `p ∤ r`, there is an `r`-th root of unity `ζ` with `ζ⁻¹ ≠ ζ` (a primitive one). -/
theorem exists_root_inv_ne (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 3 ≤ r) (hpr : ¬ p ∣ r) :
    ∃ ζ : AlgebraicClosure (ZMod p),
      ζ ∈ Polynomial.nthRootsFinset r (1 : AlgebraicClosure (ZMod p)) ∧ ζ⁻¹ ≠ ζ := by
  haveI : NeZero (r : AlgebraicClosure (ZMod p)) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]; exact hpr⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod p)) r
  refine ⟨ζ, (Polynomial.mem_nthRootsFinset (by omega) 1).2 hζ.pow_eq_one, ?_⟩
  intro h
  have h0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have h2 : ζ ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel₀ h0
  have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 h2)
  omega

/-- **Part E, (E1)–(E2)** of `q_even_assembly.md`, for every prime `p` at once: for every prime
`p`, `v ≥ 1`, `q = p^v` and every `a`, over `K = AlgebraicClosure (ZMod p)`:
`finrank K (Ibal K q a) = Nbal a q` and `finrank K (Iph K q a) = Nph a q`. (Take `r = 3` if
`p ≠ 3` and `r = 5` if `p = 3`, `S := algClosureSetting p v _ r _ _`, `ζ` a primitive `r`-th root of
unity; `bip_of_setting`.) **More general:** this covers (E1) (`p = 2`) and (E2) (odd `p`). -/
theorem E_prime (p : ℕ) [Fact p.Prime] {v : ℕ} (hv : 1 ≤ v) (a : ℕ) :
    Module.finrank (AlgebraicClosure (ZMod p))
        ((Bip.Ibal (AlgebraicClosure (ZMod p)) (p ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod p))) = Bip.Nbal a (p ^ v) ∧
      Module.finrank (AlgebraicClosure (ZMod p))
        ((Bip.Iph (AlgebraicClosure (ZMod p)) (p ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod p))) = Bip.Nph a (p ^ v) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨r, hr3, hpr⟩ : ∃ r : ℕ, 3 ≤ r ∧ ¬ p ∣ r := by
    by_cases h3 : p = 3
    · subst h3; exact ⟨5, by norm_num, by norm_num⟩
    · refine ⟨3, le_refl _, fun h => h3 ?_⟩
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  obtain ⟨ζ, hζ, hzi⟩ := exists_root_inv_ne p r hr3 hpr
  exact bip_of_setting (S := algClosureSetting p v hv r (by omega) hpr) hζ hzi a

/-- **Part E, (E1)** of `q_even_assembly.md`: **Corollary 9.12 (ii).** For every `v ≥ 1`,
`q = 2^v` and every `a`, with `K = AlgebraicClosure (ZMod 2)`:
`finrank K ((Bip.Ibal K q a).restrictScalars K) = Bip.Nbal a q` and
`finrank K ((Bip.Iph K q a).restrictScalars K) = Bip.Nph a q`. (`E_prime` at `p = 2`, with
`r = 3`, i.e. `m = 3q`.) -/
theorem E1 {v : ℕ} (hv : 1 ≤ v) (a : ℕ) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Ibal (AlgebraicClosure (ZMod 2)) (2 ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nbal a (2 ^ v) ∧
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Iph (AlgebraicClosure (ZMod 2)) (2 ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nph a (2 ^ v) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  E_prime 2 hv a

/-- **Part E, (E2)** of `q_even_assembly.md`: **Corollary 7.8** (odd `p`, the same argument). For
every odd prime `p`, `v ≥ 1`, `q = p^v` and every `a`, with `K = AlgebraicClosure (ZMod p)`:
`finrank K (Ibal K q a) = Nbal a q` and `finrank K (Iph K q a) = Nph a q`. (`E_prime`, with
`r = 3` if `p ≠ 3` and `r = 5` if `p = 3`.) The hypothesis `p ≠ 2` is not used (`E_prime` holds
for every prime). -/
theorem E2 (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) {v : ℕ} (hv : 1 ≤ v) (a : ℕ) :
    Module.finrank (AlgebraicClosure (ZMod p))
        ((Bip.Ibal (AlgebraicClosure (ZMod p)) (p ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod p))) = Bip.Nbal a (p ^ v) ∧
      Module.finrank (AlgebraicClosure (ZMod p))
        ((Bip.Iph (AlgebraicClosure (ZMod p)) (p ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod p))) = Bip.Nph a (p ^ v) :=
  E_prime p hv a

end EvenAll

end
