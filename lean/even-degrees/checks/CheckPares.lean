import RequestProject.EvenAll.PartBC
import RequestProject.EvenAll.PartD
import RequestProject.EvenAll.PartE
import RequestProject.OddEquality.PartD
import RequestProject.ColAssembly.Main

-- CheckPares.lean — the final check of the Lean certificate for every degree (v2).
-- Grepy Mandalay, 3 Oct 2026. Run from proyecto_lean/output-final_aristotle:
--   lake env lean ../../checks/CheckPares.lean
-- Prints, verbatim: the final theorem (Main Theorem′ for every m ≥ 1), its definitions, Theorem O
-- with equality and freeness, and the axioms of every main theorem; restates the final theorem
-- by hand; and evaluates the count at small degrees by kernel computation (`decide`).

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColUpper ColAssembly

-- 1. The final theorem, verbatim.
#check @EvenAll.mainTheorem'
#check @ColAssembly.mainTheorem'
#check @EvenAll.B1
#check @EvenAll.B2
#check @EvenAll.A3
#check @OddEquality.D1
#check @OddEquality.D2_DJ
#check @OddEquality.D2_M
#check @OddTheorem.theoremO

-- 2. The definitions it uses, verbatim.
#print EvenAll.Qall
#print EvenCount.QkEven
#print TheoremB.Qk
#print ColAssembly.idealZ
#print ColAssembly.RZ
#print ColAssembly.IZ
#print ColUpper.psiP
#print ColUpper.tP
#print ColSurv.phi
#print BallotBound.Matching
#print ColSplit.gaIdeal
#print ColSplit.GA
#print ColUpper.IK
#print ColUpper.psiG
#print ColUpper.tU

-- 3. Axioms.
#print axioms EvenAll.mainTheorem'
#print axioms EvenAll.B1
#print axioms EvenAll.B2
#print axioms EvenAll.A3
#print axioms ColAssembly.mainTheorem'
#print axioms OddEquality.D1
#print axioms OddEquality.D2_DJ
#print axioms OddEquality.D2_M
#print axioms OddTheorem.theoremO
#print axioms EvenCount.card_closedPointed
#print axioms EvenCount.card_Gamma_even

-- 4. The final theorem restated by hand (every m ≥ 1, every k, every field in Type).
example (m k : ℕ) (hm : 1 ≤ m) :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - EvenAll.Qall m k) ∧
    ∀ (F : Type) [Field F],
      Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - EvenAll.Qall m k ∧
        Module.finrank F ((IK F m k).restrictScalars F) = EvenAll.Qall m k :=
  ⟨(EvenAll.mainTheorem'.{0} hm k).1, fun F _ => (EvenAll.mainTheorem'.{0} hm k).2 F⟩

-- 5. The even-degree count is the count of the paper (Lemma 9.1): closed tuples of a pointed set.
example (h k : ℕ) :
    (EvenCount.closedPointed (EvenCount.stdPointed h) (2 * k + 2)).card =
      EvenCount.QkEven k (2 * h + 2) :=
  EvenCount.card_closedPointed (EvenCount.stdPointed h) k

-- 6. Small values by kernel computation: Q_k(4), Q_k(6) and Qall at m = 2, 3, 4, 5, 6.
example : EvenCount.QkEven 1 4 = 19 ∧ EvenCount.QkEven 2 4 = 141 ∧ EvenCount.QkEven 1 6 = 61 :=
  EvenCount.QkEven_values
example : EvenCount.QkEven 0 4 = 3 := by decide
example : EvenCount.QkEven 1 2 = 1 := by decide
example : TheoremB.Qk 1 3 = 6 := by decide
example : TheoremB.Qk 1 5 = 36 := by decide
example : EvenAll.Qall 4 1 = 19 := by unfold EvenAll.Qall; rw [if_pos (by decide)]; decide
example : EvenAll.Qall 3 1 = 6 := by unfold EvenAll.Qall; rw [if_neg (by decide)]; decide

-- 7. Non-vacuity of the final theorem at the Fermat quartic surface (m = 4, k = 1):
--    the quotient is free of rank 4^3 − 19 = 45, and its dimension over F_2, F_3 and ℚ is 45.
theorem qQall41 : EvenAll.Qall 4 1 = 19 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; decide
example :
    Module.Free ℤ (RZ 3 4 ⧸ IZ 4 1) ∧ Module.finrank ℤ (RZ 3 4 ⧸ IZ 4 1) = 45 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 4) (by norm_num) 1).1
  exact ⟨h.1, h.2.trans (by rw [qQall41]; norm_num)⟩
example :
    Module.finrank (ZMod 2) (GA (ZMod 2) 3 4 ⧸ IK (ZMod 2) 4 1) = 45 ∧
      Module.finrank (ZMod 3) (GA (ZMod 3) 3 4 ⧸ IK (ZMod 3) 4 1) = 45 ∧
        Module.finrank ℚ (GA ℚ 3 4 ⧸ IK ℚ 4 1) = 45 :=
  ⟨(((EvenAll.mainTheorem'.{0} (m := 4) (by norm_num) 1).2 (ZMod 2)).1).trans (by rw [qQall41]; norm_num),
   (((EvenAll.mainTheorem'.{0} (m := 4) (by norm_num) 1).2 (ZMod 3)).1).trans (by rw [qQall41]; norm_num),
   (((EvenAll.mainTheorem'.{0} (m := 4) (by norm_num) 1).2 ℚ).1).trans (by rw [qQall41]; norm_num)⟩

-- 8. Theorem O with equality at r = 3 (h = 1), k = 1: dimension 19 over every field.
example (F : Type) [Field F] :
    Module.finrank F ((TheoremB.DIdeal F 4 1).restrictScalars F) = 19 :=
  ((OddEquality.D1 F (h := 1) le_rfl 1).1).trans EvenCount.QkEven_values.1
