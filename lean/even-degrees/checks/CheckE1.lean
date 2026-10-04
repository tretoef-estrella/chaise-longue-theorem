import RequestProject.BipAny.Main
import RequestProject.BipInd.Main
#check @BipAny.thm76_any
#check @BipAny.theoremC_any
#check @BipAny.choose_pred_prime_pow
#check @BipAny.choose_pred_prime_pow_ne_zero
#check @BipAny.thm76_prime_pow
#check @BipAny.theoremC_prime_pow
#check @BipAny.lemmaS_iii
#check @BipAny.swapR_prod_sign
#check @BipAny.prop75
#check @BipAny.card_ZLam_le_of_peel
#check @Bip.thm76
#check @Bip.theoremC
#print axioms BipAny.thm76_any
#print axioms BipAny.theoremC_any
#print axioms BipAny.choose_pred_prime_pow
#print axioms BipAny.choose_pred_prime_pow_ne_zero
#print axioms BipAny.thm76_prime_pow
#print axioms BipAny.theoremC_prime_pow
#print axioms BipAny.lemmaS_iii
#print axioms BipAny.prop75
-- instances at the even box, the case the odd-degree certificate did not cover
example (F : Type) [Field F] [CharP F 2] (a : ℕ) :
    Bip.Nbal a 2 ≤ Module.finrank F ((Bip.Ibal F 2 a).restrictScalars F) ∧
      Bip.Nph a 2 ≤ Module.finrank F ((Bip.Iph F 2 a).restrictScalars F) ∧
      Bip.Nph a 2 = Bip.Nbal (a + 1) 2 :=
  BipAny.theoremC_prime_pow F (p := 2) (v := 1) Nat.prime_two le_rfl (by norm_num) a
example (F : Type) [Field F] [CharP F 2] (a : ℕ) :
    Bip.Nbal a 8 ≤ Module.finrank F ((Bip.Ibal F 8 a).restrictScalars F) ∧
      Bip.Nph a 8 ≤ Module.finrank F ((Bip.Iph F 8 a).restrictScalars F) ∧
      Bip.Nph a 8 = Bip.Nbal (a + 1) 8 :=
  BipAny.theoremC_prime_pow F (p := 2) (v := 3) Nat.prime_two (by norm_num) (by norm_num) a
