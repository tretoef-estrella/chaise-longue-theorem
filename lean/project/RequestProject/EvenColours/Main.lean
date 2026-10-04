module

public import RequestProject.EvenColours.BlockCounts
public import RequestProject.EvenColours.Closed

/-!
# (C2) and (C4) of `q_even_count_colours.md`: Lemma 9.6

* `EvenColours.C2`: Lemma 9.6 for one colouring — the number of tuples of `closedT negT (2k+2)`
  with colour tuple `cExt c` is `[comp(c)] · Π_{ζ∈SInv S} NS S ζ |𝒞_ζ| · Π_{ζ∈R} N_{bal}(|𝒞_ζ|, q)`;
* `EvenColours.C4`: Lemma 9.6, the sum over the colourings, equals `|closedT negT (2k+2)|`;
* `EvenColours.C4_even`, `EvenColours.C4_odd`: hence it equals `Q^e_k(m)` for even `m` and
  `Q_k(m)` for odd `m`.

The blocks are indexed by `SInv S ⊕ R` (as in `EvenBlocks.blocks2`); the index `0` is an ordinary
coordinate (no phantom count).  No hypothesis on the parity of `p`, `q` or `r` is made, except
`Even S.m` / `Odd S.m` in the last two statements.
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F}

variable (S) in
/-- **(C2)** of `q_even_count_colours.md` (proof, "the blocks indexed by `SInv S ⊕ R`"): the block
of a colour `x`: `inl x` if `x` is self-inverse, `inr x` if `x ∈ R`, `inr x^{−1}` if `x^{−1} ∈ R`
(and an unused default value `inl 1` for the colours outside `μ`). -/
noncomputable def blk2 (R : Finset F) (x : F) : ↥(SInv S) ⊕ ↥R :=
  if h : x ∈ SInv S then Sum.inl ⟨x, h⟩
  else if h' : x ∈ R then Sum.inr ⟨x, h'⟩
  else if h'' : x⁻¹ ∈ R then Sum.inr ⟨x⁻¹, h''⟩
  else Sum.inl ⟨1, one_mem_SInv⟩

/-- **(C2)** of `q_even_count_colours.md` (proof): `x^{−1}` is self-inverse iff `x` is. -/
theorem inv_mem_SInv_iff {x : F} : x⁻¹ ∈ SInv S ↔ x ∈ SInv S := by
  constructor
  · intro h
    have := inv_eq_of_mem_SInv h
    rw [inv_inv] at this
    rw [this]
    exact h
  · intro h
    rw [inv_eq_of_mem_SInv h]
    exact h

/-- **(C2)** of `q_even_count_colours.md` (proof): `ζ` and `ζ^{−1}` lie in the same block. -/
theorem blk2_inv {R : Finset F} (hR : IsReps2 S R) (x : F) : blk2 S R x⁻¹ = blk2 S R x := by
  by_cases h0 : x ∈ SInv S
  · rw [inv_eq_of_mem_SInv h0]
  · have h0' : x⁻¹ ∉ SInv S := fun h => h0 (inv_mem_SInv_iff.1 h)
    unfold blk2
    rw [dif_neg h0, dif_neg h0']
    by_cases h1 : x ∈ R
    · have h2 : x⁻¹ ∉ R := (hR.mem h1).2.2.2.1
      simp [h1, h2]
    · by_cases h2 : x⁻¹ ∈ R
      · simp [h1, h2]
      · simp [h1, h2]

/-- **(C2)** of `q_even_count_colours.md` (proof): for `x ∈ μ`, `x` is in the block `inl ζ` iff
`x = ζ`. -/
theorem blk2_eq_inl {R : Finset F} (hR : IsReps2 S R) {x : F} (hx : x ∈ S.μ) (ζ : ↥(SInv S)) :
    blk2 S R x = Sum.inl ζ ↔ x = ζ := by
  by_cases h0 : x ∈ SInv S
  · unfold blk2
    rw [dif_pos h0]
    simp [Subtype.ext_iff]
  · have hne : x ≠ ζ := fun h => h0 (h ▸ ζ.2)
    simp only [hne, iff_false]
    unfold blk2
    rw [dif_neg h0]
    rcases hR.cases hx with h | h | h
    · exact absurd h h0
    · rw [dif_pos h]
      simp
    · have h1 : x ∉ R := fun h1 => (hR.mem h1).2.2.2.1 h
      rw [dif_neg h1, dif_pos h]
      simp

/-- **(C2)** of `q_even_count_colours.md` (proof): for `x ∈ μ` and `ζ ∈ R`, `x` is in the block
`inr ζ` iff `x ∈ {ζ, ζ^{−1}}`. -/
theorem blk2_eq_inr {R : Finset F} (hR : IsReps2 S R) {x : F} (hx : x ∈ S.μ) (ζ : ↥R) :
    blk2 S R x = Sum.inr ζ ↔ x = ζ ∨ x = (ζ : F)⁻¹ := by
  obtain ⟨z, hz⟩ := ζ
  have hzm := hR.mem hz
  by_cases h0 : x ∈ SInv S
  · unfold blk2
    rw [dif_pos h0]
    simp only [reduceCtorEq, false_iff, not_or]
    refine ⟨fun h => hzm.2.1 (h ▸ h0), fun h => hzm.2.2.1 (h ▸ h0)⟩
  · unfold blk2
    rw [dif_neg h0]
    by_cases h1 : x ∈ R
    · rw [dif_pos h1]
      simp only [Sum.inr.injEq, Subtype.mk.injEq]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exfalso
          subst h
          exact hzm.2.2.2.1 h1
    · rw [dif_neg h1]
      by_cases h2 : x⁻¹ ∈ R
      · rw [dif_pos h2]
        simp only [Sum.inr.injEq, Subtype.mk.injEq]
        constructor
        · intro h
          right
          rw [← h, inv_inv]
        · rintro (h | h)
          · exact absurd (h ▸ hz) h1
          · rw [h, inv_inv]
      · rcases hR.cases hx with h | h | h
        · exact absurd h h0
        · exact absurd h h1
        · exact absurd h h2

/-- **(C2)** of `q_even_count_colours.md` (Lemma 9.6, one colouring): for every `k`, every
`c : Fin (2k+1) → μ` and every `R` with `IsReps2 S R`, the number of tuples
`g ∈ closedT negT (2k+2)` whose colour tuple `((g i).1.2)_i` is the extended colouring `cExt c` is
`(Π_{ζ∈SInv S} NS S ζ |𝒞_ζ|) · Π_{ζ∈R} N_{bal}(|𝒞_ζ|, q)` if some matching is compatible with
`cExt c`, and `0` otherwise.  Every pair block contributes `Bip.Nbal (|𝒞_ζ|) q`: the index `0` is an
ordinary coordinate (no phantom count). -/
theorem C2 {R : Finset F} (hR : IsReps2 S R) (k : ℕ) (c : Fin (2 * k + 1) → S.μ) :
    ((closedT (negT S) (2 * k + 2)).filter
        fun g => ∀ i, ((g i).1.2 : F) = cExt c i).card =
      if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) *
          ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
      else 0 := by
  have hκ : ∀ i, cExt c i ∈ S.μ := cExt_mem c
  split_ifs with hcomp
  · have hsz := ((existsA9 hR hκ).1 hcomp).2
    rw [card_col_eq_card_good _ hκ,
      card_good_eq_prod (X := Fin (2 * k + 2)) (blk2 S R) (blk2_inv hR) (cExt c),
      Fintype.prod_sum_type]
    congr 1
    · rw [← Finset.prod_coe_sort (SInv S) (fun ζ => NS S ζ (cls (cExt c) ζ).card)]
      refine Finset.prod_congr rfl fun ζ _ => ?_
      have hcard : Fintype.card {v // blk2 S R (cExt c v) = Sum.inl ζ} =
          (cls (cExt c) ζ).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext v
        simp [cls, blk2_eq_inl hR (hκ v)]
      rw [← hcard]
      exact card_good_self (fun j : {v // blk2 S R (cExt c v) = Sum.inl ζ} => cExt c j.1) (fun j => (blk2_eq_inl hR (hκ j.1) ζ).1 j.2)
        (inv_eq_of_mem_SInv ζ.2)
    · rw [← Finset.prod_coe_sort R (fun ζ => Bip.Nbal (cls (cExt c) ζ).card S.q)]
      refine Finset.prod_congr rfl fun ζ _ => ?_
      refine card_good_pair (fun j : {v // blk2 S R (cExt c v) = Sum.inr ζ} => cExt c j.1) (hR.mem ζ.2).2.2.2.2 ?_ ?_ ?_
      · intro j
        exact (blk2_eq_inr hR (hκ j.1) ζ).1 j.2
      · refine (ColCount.card_filter_subtype _ (fun v => cExt c v = ζ)).trans ?_
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk2_eq_inr hR (hκ v), cls]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨Or.inl h, h⟩
      · refine (ColCount.card_filter_subtype _ (fun v => cExt c v = (ζ : F)⁻¹)).trans ?_
        rw [hsz ζ ζ.2]
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk2_eq_inr hR (hκ v), cls]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨Or.inr h, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g hg hcol
    exact hcomp (exists_compatible hR hg hcol)

/-- **(C4)** of `q_even_count_colours.md` (Lemma 9.6, the sum): for every `k` and every `R` with
`IsReps2 S R`,
`Σ_{c ∈ μ^{2k+1}} [comp(c)] · (Π_{ζ∈SInv S} NS S ζ |𝒞_ζ|) · Π_{ζ∈R} N_{bal}(|𝒞_ζ|, q)
  = |closedT negT (2k+2)|`.
(Proof as `ColCount.lemma68_iii`: partition the closed tuples by their colours at the indices
`j.succ`, and use (C1) for the index `0` and (C2).) -/
theorem C4 {R : Finset F} (hR : IsReps2 S R) (k : ℕ) :
    ∑ c : Fin (2 * k + 1) → S.μ,
        (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
          (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) *
            ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
        else 0) = (closedT (negT S) (2 * k + 2)).card := by
  simp_rw [← C2 hR k]
  symm
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun (g : Fin (2 * k + 2) → T2 S) (j : Fin (2 * k + 1)) => (g j.succ).1.2)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ext g
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hg, rfl⟩
    exact ⟨hg, fun i => col_eq_cExt hg i⟩
  · rintro ⟨hg, h⟩
    refine ⟨hg, funext fun j => Subtype.ext ?_⟩
    simpa [cExt] using h j.succ

/-- **(C4)** of `q_even_count_colours.md`, even `m`: if `Even S.m`, the sum of Lemma 9.6 equals
`Q^e_k(m)` (by (C4) and (C0)(iv)). -/
theorem C4_even {R : Finset F} (hR : IsReps2 S R) (k : ℕ) (h : Even S.m) :
    ∑ c : Fin (2 * k + 1) → S.μ,
        (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
          (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) *
            ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
        else 0) = EvenCount.QkEven k S.m := by
  rw [C4 hR k]
  exact (C0_iv S h).2 k

/-- **(C4)** of `q_even_count_colours.md`, odd `m`: if `Odd S.m`, the sum of Lemma 9.6 equals
`Q_k(m)` (by (C4) and (C0)(v)). -/
theorem C4_odd {R : Finset F} (hR : IsReps2 S R) (k : ℕ) (h : Odd S.m) :
    ∑ c : Fin (2 * k + 1) → S.μ,
        (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
          (∏ ζ ∈ SInv S, NS S ζ (cls (cExt c) ζ).card) *
            ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
        else 0) = Qk k S.m := by
  rw [C4 hR k]
  exact (C0_v S h).2 k

end EvenColours

end
