import RequestProject.EvenAll.PartBC
import RequestProject.OddEquality.PartD
import RequestProject.RankTwo.Update

/-! CheckTheoremO.lean — Grepy Mandalay, 4 October 2026, after the cold reading LEAN_2.
Run from the project root (`output-final_aristotle/`, in the repository `lean/project/`):
  lake env lean ../../checks/CheckTheoremO.lean      (author's layout)
  lake env lean ../even-degrees/checks/CheckTheoremO.lean   (repository layout)
1. The seventeen definitions behind Theorem O, printed verbatim (finding F-7 of the reading).
2. The axioms of `RankTwo.R4'`, the literal form of Lemma 8.8(ii) of the paper (finding F-6).
3. Two consequences of the final theorem, proved here by the kernel (suggestion 2 of the reading;
   the proofs follow the cold reader's file `L1_main.lean`, with credit):
   (a) the subtraction `m^(2k+1) - Qall m k` never truncates, for every `m ≥ 1`, every `k`;
   (b) a non-vacuous instance where both kinds of prime divide `m`: `m = 6`, `k = 1`. -/

set_option synthInstance.maxHeartbeats 200000

-- 1. The definitions behind Theorem O
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

-- the statements of Theorem O with equality, again, for reference
#check @OddEquality.D1
#check @OddEquality.D2_DJ
#check @OddEquality.D2_M

-- 2. Lemma 8.8(ii) in the literal form of the paper
#check @RankTwo.R4'
#print axioms RankTwo.R4'

open ColSplit ColUpper ColAssembly

-- 3a. No truncation, derived from the final theorem
theorem cto_Qall_le (m k : ℕ) (hm : 1 ≤ m) : EvenAll.Qall m k ≤ m ^ (2 * k + 1) := by
  have h := ((EvenAll.mainTheorem'.{0} hm k).2 ℚ).2
  haveI := ColSplit.finite_GA (F := ℚ) (2 * k + 1) m (by omega)
  rw [← h, ← ColUpper.finrank_GA ℚ (2 * k + 1) m (by omega)]
  exact Submodule.finrank_le _

theorem cto_Qall61 : EvenAll.Qall 6 1 = 61 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.2.2

instance cto_fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- 3b. m = 6, k = 1: free of rank 155 = 216 - 61, finite, and dimension 155 over F_2, F_3, F_5, Q
theorem cto_six :
    (Module.Free ℤ (RZ 3 6 ⧸ IZ 6 1) ∧ Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1) ∧
      Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155) ∧
    Module.finrank (ZMod 2) (GA (ZMod 2) 3 6 ⧸ IK (ZMod 2) 6 1) = 155 ∧
    Module.finrank (ZMod 3) (GA (ZMod 3) 3 6 ⧸ IK (ZMod 3) 6 1) = 155 ∧
    Module.finrank (ZMod 5) (GA (ZMod 5) 3 6 ⧸ IK (ZMod 5) 6 1) = 155 ∧
    Module.finrank ℚ (GA ℚ 3 6 ⧸ IK ℚ 6 1) = 155 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).1
  haveI := h.1
  have h155 : Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by
    rw [h.2, cto_Qall61] <;> norm_num
  refine ⟨⟨h.1, Module.finite_of_finrank_pos (by rw [h155]; norm_num), h155⟩, ?_, ?_, ?_, ?_⟩
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 2)).1).trans (by rw [cto_Qall61] <;> norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 3)).1).trans (by rw [cto_Qall61] <;> norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 (ZMod 5)).1).trans (by rw [cto_Qall61] <;> norm_num)
  · exact (((EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).2 ℚ).1).trans (by rw [cto_Qall61] <;> norm_num)

#print axioms cto_Qall_le
#print axioms cto_six
