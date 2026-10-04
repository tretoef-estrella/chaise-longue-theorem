import RequestProject.EvenAll.PartBC
import RequestProject.EvenAll.PartD
import RequestProject.EvenAll.PartE
import RequestProject.OddEquality.PartD
import RequestProject.ColAssembly.Main
import RequestProject.EvenOne.Main
import RequestProject.EvenMinus.MinusMain
import RequestProject.RankTwo.Update
import RequestProject.OddTheorem.TheoremO
import RequestProject.Pow2.Main

-- L1_main.lean — Grepy Sello (cold reader, mission LEAN_2), 4 Oct 2026.
-- Run from material/project:  lake env lean ../../checks/L1_main.lean   (under vigia.sh, Lean cap)
-- 1. the final statement and Theorem O, verbatim; 2. every definition they use; 3. axioms;
-- 4. evaluation of the counts; 5. consequences derived by me from the final theorem:
--    no truncation, non-vacuous instances of my choice, the paper's own form of Main Theorem'.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColUpper ColAssembly

-- 1. statements
#check @EvenAll.mainTheorem'
#check @EvenAll.B1
#check @EvenAll.B2
#check @EvenAll.A3
#check @EvenAssembly.HypH
#check @EvenAssembly.theorem_ii
#check @EvenAssembly.theorem_iii
#check @ColAssembly.mainTheorem'
#check @ColAssembly.mainTheorem'_Z
#check @ColAssembly.mainTheorem'_field
#check @ColAssembly.finrank_IK_eq
#check @OddEquality.D1
#check @OddEquality.D2_DJ
#check @OddEquality.D2_M
#check @OddTheorem.theoremO
#check @EvenOne.E3
#check @EvenMinus.lemma99
#check @RankTwo.R4
#check @EvenCount.card_Gamma_even
#check @ColUpper.finrank_IK_eq_card_Gamma
#check @ColUpper.Gamma
#check @EvenCount.finrank_IK_le_even
#check @Pow2.q_two

-- 2. definitions
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
#print TheoremB.DIdeal
#print TheoremB.DJ
#print TheoremB.idx
#print Tight.D
#print Tight.y
#print Peel.C
#print Peel.powIdeal
#print OddEquality.Mideal
#print ColOne.DPn
#print ColComp.PerfMatch
#print OddEquality.DIdealZ
#print OddEquality.DJZ
#print OddEquality.MidealZ
#print OddEquality.DPnZ
#print EveryField.DPR
#print FreeZ.CZ
#print FreeZ.powIdealZ

-- the instances behind the field part of the final statement, fully explicit
set_option pp.explicit true in
#check fun (F : Type) [Field F] (m k : ℕ) =>
  Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k)
set_option pp.explicit true in
#check fun (F : Type) [Field F] (m k : ℕ) =>
  Module.finrank F ((IK F m k).restrictScalars F)

-- 3. axioms
#print axioms EvenAll.mainTheorem'
#print axioms EvenAll.B1
#print axioms EvenAll.B2
#print axioms EvenAll.A3
#print axioms ColAssembly.mainTheorem'
#print axioms OddEquality.D1
#print axioms OddEquality.D2_DJ
#print axioms OddEquality.D2_M
#print axioms OddTheorem.theoremO
#print axioms EvenOne.E3
#print axioms EvenMinus.lemma99
#print axioms RankTwo.R4
#print axioms EvenCount.card_Gamma_even
#print axioms EvenCount.QkEven_values

-- 4. evaluation (compiled code; the kernel proofs of some of these values are in section 5)
#eval [EvenCount.QkEven 1 4, EvenCount.QkEven 1 6, EvenCount.QkEven 2 4, EvenCount.QkEven 1 8]
#eval [TheoremB.Qk 1 3, TheoremB.Qk 1 5, TheoremB.Qk 1 7, TheoremB.Qk 1 9]
#eval [EvenCount.QkEven 0 2, EvenCount.QkEven 1 2, EvenCount.QkEven 2 2, TheoremB.Qk 0 1, TheoremB.Qk 1 1,
  TheoremB.Qk 2 1, TheoremB.Qk 0 3, EvenCount.QkEven 0 4, TheoremB.Qk 2 3, TheoremB.Qk 2 5,
  EvenCount.QkEven 2 6, TheoremB.Qk 3 3, EvenCount.QkEven 3 4, EvenCount.QkEven 1 10,
  EvenCount.QkEven 1 12, TheoremB.Qk 1 11]

-- 5. consequences derived by me

-- 5a. the subtraction in the final statement never truncates (derived from the theorem itself)
theorem gs_Qall_le (m k : ℕ) (hm : 1 ≤ m) : EvenAll.Qall m k ≤ m ^ (2 * k + 1) := by
  have h := ((EvenAll.mainTheorem'.{0} hm k).2 ℚ).2
  haveI := ColSplit.finite_GA (F := ℚ) (2 * k + 1) m (by omega)
  rw [← h, ← ColUpper.finrank_GA ℚ (2 * k + 1) m (by omega)]
  exact Submodule.finrank_le _

-- 5b. values of Qall (Qall is noncomputable: unfold, then the kernel)
theorem gs_Qall61 : EvenAll.Qall 6 1 = 61 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.2.2
theorem gs_Qall31 : EvenAll.Qall 3 1 = 6 := by
  unfold EvenAll.Qall; rw [if_neg (by decide)]; decide
theorem gs_Qall21 : EvenAll.Qall 2 1 = 1 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; decide
theorem gs_Qall51 : EvenAll.Qall 5 1 = 36 := by
  unfold EvenAll.Qall; rw [if_neg (by decide)]; decide

instance gs_fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- 5c. non-vacuous instance of my choice: m = 6, k = 1 (both kinds of prime divide 6)
example : Module.Free ℤ (RZ 3 6 ⧸ IZ 6 1) ∧ Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).1
  exact ⟨h.1, h.2.trans (by rw [gs_Qall61]; norm_num)⟩
-- the rank is positive, so the quotient is a finite free module (finrank cannot be a "0 by default")
example : Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1) := by
  have h := (EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).1
  apply Module.finite_of_finrank_pos
  rw [h.2, gs_Qall61]; norm_num
example :
    Module.finrank (ZMod 2) (GA (ZMod 2) 3 6 ⧸ IK (ZMod 2) 6 1) = 155 ∧
    Module.finrank (ZMod 3) (GA (ZMod 3) 3 6 ⧸ IK (ZMod 3) 6 1) = 155 ∧
    Module.finrank (ZMod 5) (GA (ZMod 5) 3 6 ⧸ IK (ZMod 5) 6 1) = 155 ∧
    Module.finrank ℚ (GA ℚ 3 6 ⧸ IK ℚ 6 1) = 155 ∧
    Module.finrank (ZMod 3) ((IK (ZMod 3) 6 1).restrictScalars (ZMod 3)) = 61 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 2)).1).trans (by rw [gs_Qall61]; norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 3)).1).trans (by rw [gs_Qall61]; norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 5)).1).trans (by rw [gs_Qall61]; norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 ℚ).1).trans (by rw [gs_Qall61]; norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 3)).2).trans gs_Qall61

-- 5d. the cubic surface over F_3 (paper §2.6: dim F_3[G]/(psi_J) = 21, the ideal has dimension 6)
example :
    Module.finrank (ZMod 3) (GA (ZMod 3) 3 3 ⧸ IK (ZMod 3) 3 1) = 21 ∧
    Module.finrank (ZMod 3) ((IK (ZMod 3) 3 1).restrictScalars (ZMod 3)) = 6 := by
  refine ⟨?_, ?_⟩
  · exact (((EvenAll.mainTheorem'.{0} (m := 3) (by norm_num) 1).2 (ZMod 3)).1).trans (by rw [gs_Qall31]; norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 3) (by norm_num) 1).2 (ZMod 3)).2).trans gs_Qall31

-- 5e. degenerate m = 2 (outside the paper's range): the rank is 2^3 - 1 = 7
example : Module.finrank ℤ (RZ 3 2 ⧸ IZ 2 1) = 7 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 2) (by norm_num) 1).1
  exact h.2.trans (by rw [gs_Qall21]; norm_num)

-- 5f. Main Theorem' in the paper's own form (m >= 3, k >= 1, every prime p), in a universe of my choice
example (m k : ℕ) (hm : 3 ≤ m) (hk : 1 ≤ k) (p : ℕ) [Fact p.Prime] :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - EvenAll.Qall m k) ∧
    Module.finrank (ZMod p) (GA (ZMod p) (2 * k + 1) m ⧸ IK (ZMod p) m k) =
      m ^ (2 * k + 1) - EvenAll.Qall m k :=
  ⟨(EvenAll.mainTheorem'.{0} (by omega) k).1, ((EvenAll.mainTheorem'.{0} (by omega) k).2 (ZMod p)).1⟩

-- 5g. the field part in a universe other than 0
universe w in
example (m k : ℕ) (hm : 1 ≤ m) (F : Type (w + 1)) [Field F] :
    Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) + EvenAll.Qall m k = m ^ (2 * k + 1) := by
  have h := (EvenAll.mainTheorem'.{w + 1} hm k).2 F
  rw [h.1, Nat.sub_add_cancel (gs_Qall_le m k hm)]

-- 5h. Theorem O with equality at h = 2 (r = 5), k = 1, over ZMod 2: N_5(4) = Q_1(6) = 61
#eval EvenCount.QkEven 1 6
example : Module.finrank (ZMod 2) ((TheoremB.DIdeal (ZMod 2) 6 1).restrictScalars (ZMod 2)) = 61 :=
  ((OddEquality.D1 (ZMod 2) (h := 2) (by norm_num) 1).1).trans EvenCount.QkEven_values.2.2

#print axioms gs_Qall_le
