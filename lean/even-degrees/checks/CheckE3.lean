import RequestProject.Odd3.Main

open Odd3

#check @Odd3.Z
#check @Odd3.I
#check @Odd3.card_Z_rec
#check @Odd3.card_Z_rec_zero
#check @Odd3.slices_pos
#check @Odd3.slice_zero
#check @Odd3.card_Z_le_finrank
#check @Odd3.I_odd_one_eq_DIdeal
#check @Odd3.card_Z_one_odd
#check @Odd3.O_ge_three
#check @Odd3.identity_sq
#check @Odd3.identity_vand

#print axioms Odd3.card_Z_rec
#print axioms Odd3.card_Z_rec_zero
#print axioms Odd3.slices_pos
#print axioms Odd3.slice_zero
#print axioms Odd3.card_Z_le_finrank
#print axioms Odd3.I_odd_one_eq_DIdeal
#print axioms Odd3.card_Z_one_odd
#print axioms Odd3.O_ge_three

-- Sanity of the definitions (my own examples, not Aristotle's).
example : (Odd3.Z 2 0).card = 3 := by decide
example : (Odd3.Z 3 1).card = 19 := by decide
example : (Odd3.Z 1 0).card = 1 := by decide
example : (Odd3.Z 2 5).card = 9 := by decide

-- The statement in the form the next pieces will use.
set_option synthInstance.maxHeartbeats 200000 in
example (F : Type) [Field F] (k : ℕ) :
    EvenCount.QkEven k 4 ≤ Module.finrank F ((TheoremB.DIdeal F 4 k).restrictScalars F) :=
  Odd3.O_ge_three F k

-- I(m, J) is the unit ideal for J ≥ m (first line of the Setting).
set_option synthInstance.maxHeartbeats 200000 in
example (F : Type) [Field F] : Odd3.I F 3 3 = ⊤ := by simp [Odd3.I]
