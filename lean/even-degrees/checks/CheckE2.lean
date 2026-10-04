import RequestProject.EvenCount.Main
#check @EvenCount.QkEven_eq
#check @EvenCount.QkEven_values
#check @EvenCount.mem_closedPointed_iff
#check @EvenCount.card_closedPointed
#check @EvenCount.card_Gamma_eq_card_pairs
#check @EvenCount.pointedSetting
#check @EvenCount.card_Gamma_even
#check @EvenCount.rankOver_rat_intMatU_even
#check @EvenCount.finrank_IK_le_even
#check @EvenCount.finrank_IK_eq_of_charZero_even
#check @EvenCount.theorem_iv_even
#check @ColUpper.theorem_iv
#print EvenCount.QkEven
#print EvenCount.PointedSetting
#print EvenCount.closedPointed
#print axioms EvenCount.QkEven_eq
#print axioms EvenCount.QkEven_values
#print axioms EvenCount.mem_closedPointed_iff
#print axioms EvenCount.card_closedPointed
#print axioms EvenCount.card_Gamma_eq_card_pairs
#print axioms EvenCount.card_Gamma_even
#print axioms EvenCount.rankOver_rat_intMatU_even
#print axioms EvenCount.finrank_IK_le_even
#print axioms EvenCount.finrank_IK_eq_of_charZero_even
#print axioms EvenCount.theorem_iv_even
-- the quartic: for every field F and every k, dim_F I_F ≤ QkEven k 4
set_option synthInstance.maxHeartbeats 200000 in
example (F : Type) [Field F] (k : ℕ) :
    Module.finrank F ((ColUpper.IK F 4 k).restrictScalars F) ≤ EvenCount.QkEven k 4 :=
  EvenCount.finrank_IK_le_even F (m := 4) (by decide) (by norm_num) k
