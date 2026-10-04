import RequestProject.EvenColours.Main

-- Check file for run E17 (q_even_count_colours.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE17.lean
-- Rules: every hand-restated example carries every type written out; every folder cited is
-- imported; `open scoped Classical` as in the files; implicit arguments are not passed.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColSurv ColComp TheoremB EvenBlocks EvenColours

open scoped Classical

#print EvenColours.T2
#print EvenColours.negT
#print EvenColours.closedT
#print EvenColours.NS

#check @EvenColours.card_T2
#check @EvenColours.C0_iii_even
#check @EvenColours.C0_iii_odd
#check @EvenColours.C0_iv
#check @EvenColours.C0_v
#check @EvenColours.C1
#check @EvenColours.C3_a
#check @EvenColours.C3_b
#check @EvenColours.C3_c
#check @EvenColours.C3_d
#check @EvenColours.C2
#check @EvenColours.C4
#check @EvenColours.C4_even
#check @EvenColours.C4_odd
#check @EvenColours.even_m_iff

#print axioms EvenColours.card_T2
#print axioms EvenColours.C0_iii_even
#print axioms EvenColours.C0_iii_odd
#print axioms EvenColours.C0_iv
#print axioms EvenColours.C0_v
#print axioms EvenColours.C1
#print axioms EvenColours.C3_a
#print axioms EvenColours.C3_b
#print axioms EvenColours.C3_c
#print axioms EvenColours.C3_d
#print axioms EvenColours.C2
#print axioms EvenColours.C4
#print axioms EvenColours.C4_even
#print axioms EvenColours.C4_odd
#print axioms EvenColours.even_m_iff

-- (b) closedT: balanced counts AND even counts at every fixed point, by rfl.
example (X : Type) [Fintype X] [DecidableEq X] (neg : X → X) (n : ℕ) :
    EvenColours.closedT neg n = Finset.univ.filter
      (fun g : Fin n → X => (∀ u, Fibres.cnt g u = Fibres.cnt g (neg u)) ∧
        ∀ u, neg u = u → Even (Fibres.cnt g u)) := rfl

-- (c) NS: colour 1 avoids w = 0, other colours do not, by rfl.
example (F : Type) [Field F] (S : ColSetting F) (z : F) (a : ℕ) :
    EvenColours.NS S z a =
      if z = 1 then (EvenColours.closedT (EvenColours.negW S) a).card
      else (EvenColours.closedT (fun w : ZMod S.q => -w) a).card := rfl

-- (d) (C0)(iii)-(iv) restated: one fixed point for even m; the sum Q^e_k(m).
example (F : Type) [Field F] (S : ColSetting F) (h : Even S.m) :
    ∃! x : EvenColours.T2 S, EvenColours.negT S x = x := EvenColours.C0_iii_even S h
example (F : Type) [Field F] (S : ColSetting F) (h : Even S.m) (k : ℕ) :
    (EvenColours.closedT (EvenColours.negT S) (2 * k + 2)).card = EvenCount.QkEven k S.m :=
  (EvenColours.C0_iv S h).2 k

-- (C3)(b), (c) restated.
example (F : Type) [Field F] (S : ColSetting F) (hp : S.p = 2) (k' : ℕ) :
    EvenColours.NS S 1 (2 * k' + 2) = EvenCount.QkEven k' S.q := (EvenColours.C3_b S hp).2 k'
example (F : Type) [Field F] (S : ColSetting F) (h : (-1 : F) ≠ 1) (k' : ℕ) :
    EvenColours.NS S (-1) (2 * k' + 2) = EvenCount.QkEven k' (S.q + 1) :=
  (EvenColours.C3_c S h).2 k'

-- (e) (C2) restated: one colouring, no phantom, Nbal on every pair block.
example (F : Type) [Field F] (S : ColSetting F) (R : Finset F) (hR : EvenBlocks.IsReps2 S R)
    (k : ℕ) (c : Fin (2 * k + 1) → S.μ) :
    ((EvenColours.closedT (EvenColours.negT S) (2 * k + 2)).filter
        fun g => ∀ i, ((g i).1.2 : F) = ColSurv.cExt c i).card =
      if ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J then
        (∏ z ∈ EvenBlocks.SInv S, EvenColours.NS S z (ColComp.cls (ColSurv.cExt c) z).card) *
          ∏ z ∈ R, Bip.Nbal (ColComp.cls (ColSurv.cExt c) z).card S.q
      else 0 := EvenColours.C2 hR k c

-- (g) (C4), Lemma 9.6, even m restated.
example (F : Type) [Field F] (S : ColSetting F) (R : Finset F) (hR : EvenBlocks.IsReps2 S R)
    (k : ℕ) (h : Even S.m) :
    ∑ c : Fin (2 * k + 1) → S.μ,
        (if ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J then
          (∏ z ∈ EvenBlocks.SInv S, EvenColours.NS S z (ColComp.cls (ColSurv.cExt c) z).card) *
            ∏ z ∈ R, Bip.Nbal (ColComp.cls (ColSurv.cExt c) z).card S.q
        else 0) = EvenCount.QkEven k S.m := EvenColours.C4_even hR k h
