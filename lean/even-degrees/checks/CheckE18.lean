import RequestProject.EvenMinus.Main

-- Check file for run E18 (q_even_block_minus.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE18.lean
-- Rules: every hand-restated example carries every type written out; every folder cited is
-- imported; `open scoped Classical` as in the files; implicit arguments are not passed.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColSurv ColComp ColDecomp EvenBlocks EvenColours

open scoped Classical

#check @EvenMinus.lemma67_i_gen
#check @EvenMinus.lemma67_i_reps2
#check @EvenMinus.lemma67_ii_reps2
#check @EvenMinus.lemma67_iii_bal_reps2
#check @EvenMinus.lemma67_iii_ph_reps2
#check @EvenMinus.lemma67_iii_ph'_reps2
#check @EvenMinus.lemma67_iii_ne_reps2
#check @EvenMinus.lemma67_iv_reps2
#check @EvenMinus.lemma67_vi_reps2
#check @EvenMinus.lemma97
#check @EvenMinus.lemma98
#check @EvenMinus.lemmaM1
#check @EvenMinus.lemmaM2
#check @EvenMinus.lemmaM3
#check @EvenMinus.add_pow_eq_Dab
#check @EvenMinus.D_succ_eq
#check @EvenMinus.lemmaM4
#check @EvenMinus.lemmaM4_coord
#check @EvenMinus.lemmaM5
#check @EvenMinus.lemmaM6
#check @EvenMinus.lemma99
#check @EvenMinus.S1

#print axioms EvenMinus.lemma67_i_gen
#print axioms EvenMinus.lemma67_i_reps2
#print axioms EvenMinus.lemma67_ii_reps2
#print axioms EvenMinus.lemma67_iii_bal_reps2
#print axioms EvenMinus.lemma67_iii_ph_reps2
#print axioms EvenMinus.lemma67_iii_ph'_reps2
#print axioms EvenMinus.lemma67_iii_ne_reps2
#print axioms EvenMinus.lemma67_iv_reps2
#print axioms EvenMinus.lemma67_vi_reps2
#print axioms EvenMinus.lemma97
#print axioms EvenMinus.lemma98
#print axioms EvenMinus.lemmaM1
#print axioms EvenMinus.lemmaM2
#print axioms EvenMinus.lemmaM3
#print axioms EvenMinus.add_pow_eq_Dab
#print axioms EvenMinus.D_succ_eq
#print axioms EvenMinus.lemmaM4
#print axioms EvenMinus.lemmaM4_coord
#print axioms EvenMinus.lemmaM5
#print axioms EvenMinus.lemmaM6
#print axioms EvenMinus.lemma99
#print axioms EvenMinus.S1

-- (P3) Lemma 9.7 restated: every prime (no p ≠ 2), IsReps2, index 0 an ordinary coordinate.
example (F : Type) [Field F] (S : ColSetting F) (R : Finset F) (hR : EvenBlocks.IsReps2 S R)
    (ζ : F) (hζ : ζ ∈ R) (k : ℕ) (c : Fin (2 * k + 1) → S.μ)
    (hAB : (ColComp.cls (ColSurv.cExt c) ζ).card = (ColComp.cls (ColSurv.cExt c) ζ⁻¹).card) :
    Bip.Nbal (ColComp.cls (ColSurv.cExt c) ζ).card S.q ≤
      Module.finrank F (ColDecomp.Icz S c ζ) :=
  EvenMinus.lemma97 hR hζ c hAB

-- (Q1) Lemma 9.8 restated: only S.p ≠ 2.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p ≠ 2) (k : ℕ)
    (c : Fin (2 * k + 1) → S.μ) :
    EvenColours.NS S 1 (ColComp.cls (ColSurv.cExt c) 1).card ≤
      Module.finrank F (EvenBlocks.IcS S c 1) :=
  EvenMinus.lemma98 hp c

-- (M7) Lemma 9.9 restated: only (−1 : F) ≠ 1.
example (F : Type) [Field F] (S : ColSetting F) (hneg : (-1 : F) ≠ 1) (k : ℕ)
    (c : Fin (2 * k + 1) → S.μ) :
    EvenColours.NS S (-1) (ColComp.cls (ColSurv.cExt c) (-1)).card ≤
      Module.finrank F (EvenBlocks.IcS S c (-1)) :=
  EvenMinus.lemma99 S hneg c

-- (M5) restated: 0 ∈ 𝒞_{−1}, size 2j+2: the block is the odd box r = q (Theorem B ideal at q+1).
example (F : Type) [Field F] (S : ColSetting F) (hneg : (-1 : F) ≠ 1) (k j : ℕ)
    (c : Fin (2 * k + 1) → S.μ) (h0 : (0 : Fin (2 * k + 2)) ∈ ColComp.cls (ColSurv.cExt c) (-1))
    (hs : (ColComp.cls (ColSurv.cExt c) (-1)).card = 2 * j + 2) :
    Module.finrank F (EvenBlocks.IcS S c (-1)) =
      Module.finrank F ((TheoremB.DIdeal F (S.q + 1) j).restrictScalars F) :=
  (EvenMinus.lemmaM5 S hneg c h0 hs).1

-- (M6) restated: 0 ∉ 𝒞_{−1}, size 2j+2: the block is V for the root shape, h = (q−1)/2.
example (F : Type) [Field F] (S : ColSetting F) (hneg : (-1 : F) ≠ 1) (k j : ℕ)
    (c : Fin (2 * k + 1) → S.μ) (h0 : (0 : Fin (2 * k + 2)) ∉ ColComp.cls (ColSurv.cExt c) (-1))
    (hs : (ColComp.cls (ColSurv.cExt c) (-1)).card = 2 * j + 2) :
    Module.finrank F (EvenBlocks.IcS S c (-1)) =
      Module.finrank F ((OddPatterns.VSAll F ((S.q - 1) / 2) (2 * j + 2)
        {(OddShapes.emptyPart, false)}).restrictScalars F) :=
  (EvenMinus.lemmaM6 S hneg c h0 hs).1

-- (M3) restated: (a+b)^(q−1) = ColOne.Dab (q+1) a b, every prime (2 included).
example (F : Type) [Field F] (S : ColSetting F) (A : Type) [CommRing A] [Algebra F A] (a b : A) :
    (a + b) ^ (S.q - 1) = ColOne.Dab (S.q + 1) a b :=
  EvenMinus.add_pow_eq_Dab S a b

-- (S1) restated.
example (F : Type) [Field F] (S : ColSetting F) (R : Finset F) (hR : EvenBlocks.IsReps2 S R)
    (k : ℕ) (c : Fin (2 * k + 1) → S.μ)
    (hcomp : ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) :
    (S.p ≠ 2 → EvenColours.NS S 1 (ColComp.cls (ColSurv.cExt c) 1).card ≤
        Module.finrank F (EvenBlocks.IcS S c 1)) ∧
      ((-1 : F) ≠ 1 → EvenColours.NS S (-1) (ColComp.cls (ColSurv.cExt c) (-1)).card ≤
        Module.finrank F (EvenBlocks.IcS S c (-1))) ∧
      ∀ ζ ∈ R, Bip.Nbal (ColComp.cls (ColSurv.cExt c) ζ).card S.q ≤
        Module.finrank F (ColDecomp.Icz S c ζ) :=
  EvenMinus.S1 S hR c hcomp
