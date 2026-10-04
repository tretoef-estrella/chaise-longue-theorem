import RequestProject.EvenAssembly.Quartic

#check @EvenAssembly.HypH
#print EvenAssembly.HypH
#check @EvenAssembly.theorem_i
#check @EvenAssembly.theorem_ii
#check @EvenAssembly.theorem_iii
#check @EvenAssembly.hypH_four
#check @EvenAssembly.every_field_four
#check @EvenAssembly.mainTheorem'_four
#check @ColAssembly.mainTheorem'

#print axioms EvenAssembly.theorem_i
#print axioms EvenAssembly.theorem_ii
#print axioms EvenAssembly.theorem_iii
#print axioms EvenAssembly.hypH_four
#print axioms EvenAssembly.every_field_four
#print axioms EvenAssembly.mainTheorem'_four

-- My own instances (not Aristotle's): Main Theorem' at m = 4, k = 1 with the numbers written out.
set_option synthInstance.maxHeartbeats 200000 in
example :
    Module.Free ℤ (ColAssembly.RZ 3 4 ⧸ ColAssembly.IZ 4 1) ∧
      Module.finrank ℤ (ColAssembly.RZ 3 4 ⧸ ColAssembly.IZ 4 1) = 45 := by
  have h := (EvenAssembly.mainTheorem'_four 1).1
  have hQ : EvenCount.QkEven 1 4 = 19 := EvenCount.QkEven_values.1
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [hQ] at h2
  simpa using h2

-- and over the rationals and over F_3: dim I = 19 at k = 1.
set_option synthInstance.maxHeartbeats 200000 in
example : Module.finrank ℚ ((ColUpper.IK ℚ 4 1).restrictScalars ℚ) = 19 := by
  rw [(EvenAssembly.every_field_four ℚ 1).2]; exact EvenCount.QkEven_values.1
