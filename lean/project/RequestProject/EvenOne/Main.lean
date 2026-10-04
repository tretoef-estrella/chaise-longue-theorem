module

public import RequestProject.EvenOne.CaseOut
public import RequestProject.EvenOne.Checks

/-!
# `q_even_block_one.md`: the block of colour `1` at the prime `2` (Lemma 9.10) and the lower bound
for every `ColSetting`

This file imports every file of `RequestProject/EvenOne/`:
* Part A: `Phi.lean`; Part B: `CaseIn.lean`; Part C: `Theta.lean` ((C1)–(C3)) and `CaseOut.lean`
  ((C4), (C5)); the numerical values of the checks: `Checks.lean`;

and proves
* Part D: (D1) `EvenOne.lemma910` (Lemma 9.10);
* Part E: (E1) `EvenOne.E1`, (E2) `EvenOne.E2`, (E3) `EvenOne.E3` (Theorem 9.11, `≥`, over `F`).
-/

@[expose] public section

open MvPolynomial

namespace EvenOne

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-! ### Part D -/

/-- **Part D, (D1)** of `q_even_block_one.md` (size `0`; the analogue of
`EvenMinus.finrank_IcS_of_card_eq_zero` for the colour `1`): if `𝒞_1 = ∅`, then
`I_{c,1} = B(∅)` has dimension `1` (the empty matching gives the generator `1`). -/
theorem finrank_IcS_one_of_card_eq_zero (c : Fin (2 * k + 1) → S.μ)
    (hs : (cls (cExt c) 1).card = 0) : Module.finrank F (IcS S c 1) = 1 := by
  have hcls : cls (cExt c) 1 = ∅ := Finset.card_eq_zero.1 hs
  have hW : WS S c 1 = ∅ := by
    ext j
    simp [EvenMinus.mem_WS, hcls]
  haveI : IsEmpty (cls (cExt c) 1) := ⟨fun x => by simpa [hcls] using x.2⟩
  have htop : IcS S c 1 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    let P : PerfMatch (cls (cExt c) 1) := ⟨fun x => x, fun x => isEmptyElim x⟩
    have hP : gPS S c 1 P = 1 := by
      rw [gPS, Finset.univ_eq_empty, Finset.filter_empty, Finset.prod_empty]
    rw [← hP]
    exact Ideal.subset_span ⟨P, rfl⟩
  rw [htop, ColTensor.finrank_top_ideal]
  exact (boxS S c).finrank_box_of_eq_empty hW

/-- **Part D, (D1)** of `q_even_block_one.md`: **Lemma 9.10.** If `S.p = 2`, then for every
colouring `c`, `EvenColours.NS S 1 |𝒞_1| ≤ finrank F (EvenBlocks.IcS S c 1)`. (Size `0`: both
sides are `1` (`EvenColours.C3_b`); size `2j + 2`: `EvenColours.C3_b` with (B3) if `0 ∈ 𝒞_1` or
(C5) if `0 ∉ 𝒞_1`; odd size: `EvenColours.C3_d`.) -/
theorem lemma910 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) :
    EvenColours.NS S 1 (cls (cExt c) 1).card ≤ Module.finrank F (IcS S c 1) := by
  rcases Nat.even_or_odd (cls (cExt c) 1).card with ⟨j, hj⟩ | hodd
  · rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hs : (cls (cExt c) 1).card = 0 := by omega
      rw [hs, (EvenColours.C3_b S hp).1, finrank_IcS_one_of_card_eq_zero S c hs]
    · have hs : (cls (cExt c) 1).card = 2 * (j - 1) + 2 := by omega
      rw [hs, (EvenColours.C3_b S hp).2]
      by_cases h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1
      · exact B3 S hp c h0 hs
      · exact (C5 S hp c h0 hs).2
  · rw [EvenColours.C3_d S 1 hodd]
    exact Nat.zero_le _

/-! ### Part E -/

/-- **Part E, (E1)** of `q_even_block_one.md` (one factor): for every prime `p` and every
self-inverse colour `ζ ∈ SInv S`, `NS S ζ |𝒞_ζ| ≤ finrank F (IcS S c ζ)`. (`ζ` is `1` or `−1`
(`SInv_subset`); colour `1`: `EvenMinus.lemma98` if `S.p ≠ 2`, (D1) if `S.p = 2`; colour
`−1 ≠ 1`: `EvenMinus.lemma99`.) -/
theorem NS_le_finrank_IcS (c : Fin (2 * k + 1) → S.μ) {ζ : F} (hζ : ζ ∈ SInv S) :
    EvenColours.NS S ζ (cls (cExt c) ζ).card ≤ Module.finrank F (IcS S c ζ) := by
  by_cases h1 : ζ = 1
  · subst h1
    by_cases hp : S.p = 2
    · exact lemma910 S hp c
    · exact EvenMinus.lemma98 hp c
  · have hm : ζ = -1 := by
      have := SInv_subset (S := S) hζ
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    subst hm
    exact EvenMinus.lemma99 S h1 c

/-- **Part E, (E1)** of `q_even_block_one.md`: for every `ColSetting S` (every prime), every `R`
with `IsReps2 S R` and every `c` with a compatible matching:
`(Π_{ζ ∈ SInv S} NS S ζ |𝒞_ζ|) · Π_{ζ ∈ R} Bip.Nbal |𝒞_ζ| S.q ≤
  (Π_{ζ ∈ SInv S} finrank (IcS S c ζ)) · Π_{ζ ∈ R} finrank (Icz S c ζ)`
(factor by factor: `EvenOne.NS_le_finrank_IcS`, and `EvenMinus.lemma97` with
`|𝒞_ζ| = |𝒞_{ζ⁻¹}|` from `existsA9`). -/
theorem E1 {R : Finset F} (hR : IsReps2 S R) (c : Fin (2 * k + 1) → S.μ)
    (hcomp : ∃ J : BallotBound.Matching k, Compatible (cExt c) J) :
    (∏ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card) *
        ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q ≤
      (∏ ζ ∈ SInv S, Module.finrank F (IcS S c ζ)) *
        ∏ ζ ∈ R, Module.finrank F (Icz S c ζ) := by
  have hsz := ((existsA9 hR (cExt_mem c)).1 hcomp).2
  exact Nat.mul_le_mul
    (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun ζ hζ => NS_le_finrank_IcS S c hζ)
    (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun ζ hζ =>
      EvenMinus.lemma97 hR hζ c (hsz ζ hζ))

/-- **Part E, (E2)** of `q_even_block_one.md`: for every `c` (compatible or not), the term of
`EvenColours.C2` is at most `finrank F ((idealI S k).map (S.piC c))` (`EvenBlocks.lemma95` and
(E1)). -/
theorem E2 {R : Finset F} (hR : IsReps2 S R) (c : Fin (2 * k + 1) → S.μ) :
    (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        (∏ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card) *
          ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
      else 0) ≤ Module.finrank F ((idealI S k).map (S.piC c)) := by
  split_ifs with hcomp
  · rw [(lemma95 S c hR).1 hcomp]
    exact E1 S hR c hcomp
  · exact Nat.zero_le _

/-- **Part E, (E3)** of `q_even_block_one.md`: **Theorem 9.11, `≥`, over `F`.** For every
`ColSetting S` (every prime `p`, `2` included, every cofactor `r`) and every `k`:
`card (closedT negT (2k+2)) ≤ finrank F ((idealI S k).restrictScalars F)`; hence
`EvenCount.QkEven k S.m ≤ finrank F (idealI S k)` if `Even S.m`, and
`TheoremB.Qk k S.m ≤ finrank F (idealI S k)` if `Odd S.m`. (`lemma61_ii` writes `dim I` as the
sum over `c` of `dim π_c(I)`; (E2) and `EvenColours.C4`, `C4_even`, `C4_odd`.) -/
theorem E3 (k : ℕ) :
    (EvenColours.closedT (EvenColours.negT S) (2 * k + 2)).card ≤
        Module.finrank F ((idealI S k).restrictScalars F) ∧
      (Even S.m → EvenCount.QkEven k S.m ≤ Module.finrank F ((idealI S k).restrictScalars F)) ∧
      (Odd S.m → TheoremB.Qk k S.m ≤ Module.finrank F ((idealI S k).restrictScalars F)) := by
  obtain ⟨R, hR⟩ := exists_isReps2 (S := S)
  have hsum : (∑ c : Fin (2 * k + 1) → S.μ,
      (if ∃ J : BallotBound.Matching k, Compatible (cExt c) J then
        (∏ ζ ∈ SInv S, EvenColours.NS S ζ (cls (cExt c) ζ).card) *
          ∏ ζ ∈ R, Bip.Nbal (cls (cExt c) ζ).card S.q
      else 0)) ≤ Module.finrank F ((idealI S k).restrictScalars F) := by
    rw [S.lemma61_ii (2 * k + 1) (idealI S k)]
    exact Finset.sum_le_sum fun c _ => E2 S hR c
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rw [← EvenColours.C4 hR k]; exact hsum
  · rw [← EvenColours.C4_even hR k h]; exact hsum
  · rw [← EvenColours.C4_odd hR k h]; exact hsum

end EvenOne

end
