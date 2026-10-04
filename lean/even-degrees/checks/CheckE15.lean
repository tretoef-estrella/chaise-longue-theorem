import RequestProject.OddEquality.PartD
import RequestProject.OddEquality.PartC3

-- Check file for run E15 (q_oddbox_equality.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE15.lean
-- Imports the theorem modules directly (PartD imports PartA, PartB, PartC, Defs, IntegralGen;
-- PartC3 holds (C3)). OddEquality.Checks (numeric `decide` checks) is checked by its own build.
-- Rules: every hand-restated example carries every type written out; every folder cited is
-- imported; implicit arguments are not passed.

set_option synthInstance.maxHeartbeats 200000

#check @OddEquality.Mideal
#check @OddEquality.IPC
#check @OddEquality.Kint
#check @OddEquality.A1
#check @OddEquality.A2
#check @OddEquality.theta
#check @OddEquality.A3
#check @OddEquality.theta_D0
#check @OddEquality.A4
#check @OddEquality.A5
#check @OddEquality.pairing_injective
#check @OddEquality.B1
#check @OddEquality.B2
#check @OddEquality.B3
#check @OddEquality.C1
#check @OddEquality.C3_ideal
#check @OddEquality.C3_top
#check @OddEquality.C4
#check @OddEquality.C5
#check @OddEquality.card_Gamma
#check @OddEquality.partC
#check @OddEquality.D1_rat
#check @OddEquality.D1
#check @OddEquality.D2_DJ
#check @OddEquality.D2_M
#check @OddEquality.partB_attained

#print OddEquality.Mideal
#print OddEquality.IPC
#print OddEquality.Kint
#print OddEquality.theta
#print OddEquality.DJZ
#print OddEquality.DIdealZ
#print OddEquality.DPnZ
#print OddEquality.MidealZ
#print FreeZ.CZ
#print EvenCount.QkEven

#print axioms OddEquality.A1
#print axioms OddEquality.A2
#print axioms OddEquality.A3
#print axioms OddEquality.A4
#print axioms OddEquality.A5
#print axioms OddEquality.B1
#print axioms OddEquality.B2
#print axioms OddEquality.B3
#print axioms OddEquality.C1
#print axioms OddEquality.C3_ideal
#print axioms OddEquality.C3_top
#print axioms OddEquality.C4
#print axioms OddEquality.C5
#print axioms OddEquality.partC
#print axioms OddEquality.D1_rat
#print axioms OddEquality.D1
#print axioms OddEquality.D2_DJ
#print axioms OddEquality.D2_M
#print axioms OddEquality.partB_attained

-- (D1) restated: Corollary 8.13 of v11, every field, h ≥ 1, every k (k = 0 included).
example (F : Type) [Field F] (h k : ℕ) (hh : 1 ≤ h) :
    Module.finrank F ((TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F) =
        EvenCount.QkEven k (2 * h + 2) ∧
      Module.finrank F ((OddEquality.Mideal F (2 * h + 2) (2 * k + 2)).restrictScalars F) =
        EvenCount.QkEven k (2 * h + 2) :=
  OddEquality.D1 F hh k

-- (D2) restated for (D_J): Theorem O, second sentence; rank r^(2k+1) − Q, r = 2h+1.
example (h k : ℕ) (hh : 1 ≤ h) :
    Module.Free ℤ (FreeZ.CZ (2 * h + 2) (2 * k + 1) ⧸ OddEquality.DIdealZ (2 * h + 2) k) ∧
      Module.finrank ℤ (FreeZ.CZ (2 * h + 2) (2 * k + 1) ⧸ OddEquality.DIdealZ (2 * h + 2) k) =
        (2 * h + 1) ^ (2 * k + 1) - EvenCount.QkEven k (2 * h + 2) :=
  OddEquality.D2_DJ hh k

-- (D2) restated for ℳ in N = 2k+2 variables.
example (h k : ℕ) (hh : 1 ≤ h) :
    Module.Free ℤ (FreeZ.CZ (2 * h + 2) (2 * k + 2) ⧸ OddEquality.MidealZ (2 * h + 2) (2 * k + 2)) ∧
      Module.finrank ℤ (FreeZ.CZ (2 * h + 2) (2 * k + 2) ⧸ OddEquality.MidealZ (2 * h + 2) (2 * k + 2)) =
        (2 * h + 1) ^ (2 * k + 2) - EvenCount.QkEven k (2 * h + 2) :=
  OddEquality.D2_M hh k

-- The inequality of E14 (OddTheorem.theoremO) is recovered from the equality: same two sides.
example (F : Type) [Field F] (h k : ℕ) (hh : 1 ≤ h) :
    EvenCount.QkEven k (2 * h + 2) ≤
      Module.finrank F ((TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F) :=
  le_of_eq (OddEquality.D1 F hh k).1.symm
