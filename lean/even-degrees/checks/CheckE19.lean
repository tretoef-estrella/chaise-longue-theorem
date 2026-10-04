import RequestProject.EvenOne.Main

-- Check file for run E19 (q_even_block_one.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE19.lean
-- Rules: every hand-restated example carries every type written out; every folder cited is
-- imported (EvenOne.Main imports EvenMinus, Pow2, EvenColours, EvenBlocks, ColUpper, TheoremB);
-- `open scoped Classical` as in the files; implicit arguments are not passed.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColSurv ColComp ColDecomp EvenBlocks EvenColours

open scoped Classical

#check @EvenOne.A1
#check @EvenOne.A1_of_two_eq_zero
#check @EvenOne.A2
#check @EvenOne.PhiE_psiG
#check @EvenOne.B1
#check @EvenOne.B2
#check @EvenOne.B3
#check @EvenOne.theta
#check @EvenOne.theta_iota_mul
#check @EvenOne.theta_pair_X
#check @EvenOne.C4
#check @EvenOne.C5
#check @EvenOne.finrank_IcS_one_of_card_eq_zero
#check @EvenOne.lemma910
#check @EvenOne.NS_le_finrank_IcS
#check @EvenOne.E1
#check @EvenOne.E2
#check @EvenOne.E3

#print axioms EvenOne.A1
#print axioms EvenOne.A1_of_two_eq_zero
#print axioms EvenOne.A2
#print axioms EvenOne.PhiE_psiG
#print axioms EvenOne.B1
#print axioms EvenOne.B2
#print axioms EvenOne.B3
#print axioms EvenOne.theta_iota_mul
#print axioms EvenOne.theta_pair_X
#print axioms EvenOne.C4
#print axioms EvenOne.C5
#print axioms EvenOne.finrank_IcS_one_of_card_eq_zero
#print axioms EvenOne.lemma910
#print axioms EvenOne.NS_le_finrank_IcS
#print axioms EvenOne.E1
#print axioms EvenOne.E2
#print axioms EvenOne.E3

-- (A1) restated: characteristic 2, q = 2^v.
example (A : Type) [CommRing A] [CharP A 2] (v : ℕ) (u : A) :
    (u - 1) ^ (2 ^ v - 1) = ColSurv.phi (2 ^ v) u ∧ (u - 1) ^ (2 ^ v) = u ^ (2 ^ v) - 1 :=
  EvenOne.A1 v u

-- (B1) restated: 0 ∈ 𝒞_1, size 2j+2: the block of colour 1 at p = 2 has the dimension of IK.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p = 2) (k j : ℕ)
    (c : Fin (2 * k + 1) → S.μ) (h0 : (0 : Fin (2 * k + 2)) ∈ ColComp.cls (ColSurv.cExt c) 1)
    (hs : (ColComp.cls (ColSurv.cExt c) 1).card = 2 * j + 2) :
    Module.finrank F (EvenBlocks.IcS S c 1) =
      Module.finrank F ((ColUpper.IK F S.q j).restrictScalars F) :=
  EvenOne.B1 S hp c h0 hs

-- (B2) restated: QkEven j q ≤ dim IK at p = 2, every j.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p = 2) (j : ℕ) :
    EvenCount.QkEven j S.q ≤ Module.finrank F ((ColUpper.IK F S.q j).restrictScalars F) :=
  EvenOne.B2 S hp j

-- (C5) restated: 0 ∉ 𝒞_1, size 2j+2.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p = 2) (k j : ℕ)
    (c : Fin (2 * k + 1) → S.μ) (h0 : (0 : Fin (2 * k + 2)) ∉ ColComp.cls (ColSurv.cExt c) 1)
    (hs : (ColComp.cls (ColSurv.cExt c) 1).card = 2 * j + 2) :
    EvenCount.QkEven j S.q ≤ Module.finrank F (EvenBlocks.IcS S c 1) :=
  (EvenOne.C5 S hp c h0 hs).2

-- (D1) Lemma 9.10 restated: only S.p = 2, every size.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p = 2) (k : ℕ)
    (c : Fin (2 * k + 1) → S.μ) :
    EvenColours.NS S 1 (ColComp.cls (ColSurv.cExt c) 1).card ≤
      Module.finrank F (EvenBlocks.IcS S c 1) :=
  EvenOne.lemma910 S hp c

-- (E1) one factor restated: every prime, every self-inverse colour.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (c : Fin (2 * k + 1) → S.μ)
    (ζ : F) (hζ : ζ ∈ EvenBlocks.SInv S) :
    EvenColours.NS S ζ (ColComp.cls (ColSurv.cExt c) ζ).card ≤
      Module.finrank F (EvenBlocks.IcS S c ζ) :=
  EvenOne.NS_le_finrank_IcS S c hζ

-- (E3) Theorem 9.11 (≥) restated: every ColSetting, no hypothesis on p, q, r.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (hm : Even S.m) :
    EvenCount.QkEven k S.m ≤ Module.finrank F ((ColDecomp.idealI S k).restrictScalars F) :=
  (EvenOne.E3 S k).2.1 hm

example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (hm : Odd S.m) :
    TheoremB.Qk k S.m ≤ Module.finrank F ((ColDecomp.idealI S k).restrictScalars F) :=
  (EvenOne.E3 S k).2.2 hm
