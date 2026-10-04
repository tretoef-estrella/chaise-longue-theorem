import RequestProject.Pow2.Main

#check @Pow2.phi_two_pow
#check @Pow2.Theta
#check @Pow2.Theta_X
#check @Pow2.exists_Theta
#check @Pow2.PJ
#check @Pow2.LJ
#check @Pow2.EJ
#check @Pow2.mk_EJ
#check @Pow2.Theta_psiG
#check @Pow2.lowest_forms
#check @Pow2.mul_add_pow
#check @Pow2.mk_LJ
#check @Pow2.prop92_ge
#check @Pow2.pow2_of_oddbox
#check @Pow2.quartic_char_two
#check @Pow2.q_two

#print axioms Pow2.phi_two_pow
#print axioms Pow2.exists_Theta
#print axioms Pow2.Theta_psiG
#print axioms Pow2.lowest_forms
#print axioms Pow2.mul_add_pow
#print axioms Pow2.mk_LJ
#print axioms Pow2.prop92_ge
#print axioms Pow2.pow2_of_oddbox
#print axioms Pow2.quartic_char_two
#print axioms Pow2.q_two

-- My own instances (not Aristotle's): the quartic over F_2, and its value at k = 1.
set_option synthInstance.maxHeartbeats 200000 in
example (k : ℕ) :
    Module.finrank (ZMod 2) ((ColUpper.IK (ZMod 2) 4 k).restrictScalars (ZMod 2)) =
      EvenCount.QkEven k 4 :=
  Pow2.quartic_char_two (ZMod 2) k

set_option synthInstance.maxHeartbeats 200000 in
example :
    Module.finrank (ZMod 2) ((ColUpper.IK (ZMod 2) 4 1).restrictScalars (ZMod 2)) = 19 := by
  rw [Pow2.quartic_char_two]; exact EvenCount.QkEven_values.1
