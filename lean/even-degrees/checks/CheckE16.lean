import RequestProject.EvenBlocks.Main
import RequestProject.ColDecomp.Main
import RequestProject.ColAssembly.EveryField

-- Check file for run E16 (q_even_blocks.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE16.lean
-- Rule: every hand-restated example carries every type written out; every folder cited is imported.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks

open scoped Classical

#print EvenBlocks.SInv
#print EvenBlocks.IsReps2
#print EvenBlocks.Tuples2
#print EvenBlocks.gPS

#check @EvenBlocks.r_ne_zero
#check @EvenBlocks.not_p_dvd_r
#check @EvenBlocks.lemma94
#check @EvenBlocks.algClosureSetting
#check @EvenBlocks.exists_setting
#check @EvenBlocks.one_mem_SInv
#check @EvenBlocks.mem_SInv_iff
#check @EvenBlocks.SInv_subset
#check @EvenBlocks.SInv_eq_singleton
#check @EvenBlocks.even_r_facts
#check @EvenBlocks.exists_isReps2
#check @EvenBlocks.isReps2_iff_isReps
#check @EvenBlocks.partitionA5
#check @EvenBlocks.pair_iff
#check @EvenBlocks.compatible_iff
#check @EvenBlocks.compEquiv2
#check @EvenBlocks.existsA9
#check @EvenBlocks.cardA9
#check @EvenBlocks.W1_eq_WS
#check @EvenBlocks.gP_eq_gPS
#check @EvenBlocks.Ic1_eq_IcS
#check @EvenBlocks.piC_psi_eq_unit_mul2
#check @EvenBlocks.map_idealI_eq_span2
#check @EvenBlocks.map_idealI_eq_bot
#check @EvenBlocks.lemma95
#check @EvenBlocks.prod_finrank_IcS_of_SInv_eq
#check @EvenBlocks.prop65_iii_of_SInv_eq

#print axioms EvenBlocks.r_ne_zero
#print axioms EvenBlocks.not_p_dvd_r
#print axioms EvenBlocks.lemma94
#print axioms EvenBlocks.algClosureSetting
#print axioms EvenBlocks.exists_setting
#print axioms EvenBlocks.one_mem_SInv
#print axioms EvenBlocks.mem_SInv_iff
#print axioms EvenBlocks.SInv_subset
#print axioms EvenBlocks.SInv_eq_singleton
#print axioms EvenBlocks.even_r_facts
#print axioms EvenBlocks.exists_isReps2
#print axioms EvenBlocks.isReps2_iff_isReps
#print axioms EvenBlocks.partitionA5
#print axioms EvenBlocks.pair_iff
#print axioms EvenBlocks.compatible_iff
#print axioms EvenBlocks.compEquiv2
#print axioms EvenBlocks.existsA9
#print axioms EvenBlocks.cardA9
#print axioms EvenBlocks.W1_eq_WS
#print axioms EvenBlocks.gP_eq_gPS
#print axioms EvenBlocks.Ic1_eq_IcS
#print axioms EvenBlocks.piC_psi_eq_unit_mul2
#print axioms EvenBlocks.map_idealI_eq_span2
#print axioms EvenBlocks.map_idealI_eq_bot
#print axioms EvenBlocks.lemma95
#print axioms EvenBlocks.prod_finrank_IcS_of_SInv_eq
#print axioms EvenBlocks.prop65_iii_of_SInv_eq

-- (a) the definition of SInv, by rfl.
example (F : Type) [Field F] (S : ColSetting F) :
    EvenBlocks.SInv S = S.μ.filter (fun z : F => z⁻¹ = z) := rfl

-- (01) restated.
example (F : Type) [Field F] (S : ColSetting F) : (S.r : F) ≠ 0 := EvenBlocks.r_ne_zero S

-- (02) restated: every prime p (2 included), v ≥ 1, r ≥ 1, p ∤ r; no parity.
example (p : ℕ) [Fact p.Prime] (v : ℕ) (hv : 1 ≤ v) (r : ℕ) (hr : 1 ≤ r) (hpr : ¬ p ∣ r) :
    ∃ S : ColSetting (AlgebraicClosure (ZMod p)), S.p = p ∧ S.v = v ∧ S.r = r ∧
      S.μ = Polynomial.nthRootsFinset r (1 : AlgebraicClosure (ZMod p)) ∧ S.m = p ^ v * r :=
  EvenBlocks.exists_setting p v hv r hr hpr

-- (02) at p = 2, r = 3 (an even degree m = 2^v * 3): the hypotheses are met.
example : ∃ S : ColSetting (AlgebraicClosure (ZMod 2)), S.p = 2 ∧ S.v = 1 ∧ S.r = 3 ∧
    S.μ = Polynomial.nthRootsFinset 3 (1 : AlgebraicClosure (ZMod 2)) ∧ S.m = 2 ^ 1 * 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact EvenBlocks.exists_setting 2 1 le_rfl 3 (by norm_num) (by norm_num)

-- (A2a) and (A2b) restated.
example (F : Type) [Field F] (S : ColSetting F) (h : Odd S.r ∨ S.p = 2) :
    EvenBlocks.SInv S = {1} := EvenBlocks.SInv_eq_singleton (S := S) h
example (F : Type) [Field F] (S : ColSetting F) (h : Even S.r) :
    S.p ≠ 2 ∧ (-1 : F) ≠ 1 ∧ (-1 : F) ∈ S.μ ∧ EvenBlocks.SInv S = {1, -1} :=
  EvenBlocks.even_r_facts (S := S) h

-- (A4) restated.
example (F : Type) [Field F] (S : ColSetting F) (h : EvenBlocks.SInv S = {1}) (R : Finset F) :
    EvenBlocks.IsReps2 S R ↔ ColComp.IsReps S R := EvenBlocks.isReps2_iff_isReps (S := S) h R

-- (A9) restated: the count.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (R : Finset F)
    (c : Fin (2 * k + 2) → F) (hR : EvenBlocks.IsReps2 S R) (hc : ∀ v, c v ∈ S.μ)
    (h1 : ∀ z ∈ EvenBlocks.SInv S, Even (ColComp.cls c z).card)
    (h2 : ∀ z ∈ R, (ColComp.cls c z).card = (ColComp.cls c z⁻¹).card) :
    Nat.card {J : BallotBound.Matching k // ColComp.Compatible c J} =
      (∏ z ∈ EvenBlocks.SInv S, ((ColComp.cls c z).card - 1).doubleFactorial) *
        ∏ z ∈ R, ((ColComp.cls c z).card).factorial :=
  EvenBlocks.cardA9 hR hc h1 h2

-- (f) the block generator of colour 1 is the old one.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (c : Fin (2 * k + 1) → S.μ) :
    ColDecomp.gP S c = EvenBlocks.gPS S c 1 := rfl
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (c : Fin (2 * k + 1) → S.μ) :
    ColDecomp.Ic1 S c = EvenBlocks.IcS S c 1 := rfl

-- (B3) Lemma 9.5 restated.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (c : Fin (2 * k + 1) → S.μ)
    (R : Finset F) (hR : EvenBlocks.IsReps2 S R) :
    ((∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) →
        Module.finrank F ((ColDecomp.idealI S k).map (S.piC c)) =
          (∏ z ∈ EvenBlocks.SInv S, Module.finrank F (EvenBlocks.IcS S c z)) *
            ∏ z ∈ R, Module.finrank F (ColDecomp.Icz S c z)) ∧
      ((¬ ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) →
        Module.finrank F ((ColDecomp.idealI S k).map (S.piC c)) = 0) :=
  EvenBlocks.lemma95 S c hR

-- (B4) next to the old prop65_iii: same statement.
example (F : Type) [Field F] (S : ColSetting F) (k : ℕ) (h : EvenBlocks.SInv S = {1})
    (c : Fin (2 * k + 1) → S.μ) (R : Finset F) (hR : ColComp.IsReps S R) :
    ((∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) →
        Module.finrank F ((ColDecomp.idealI S k).map (S.piC c)) =
          Module.finrank F (ColDecomp.Ic1 S c) * ∏ z ∈ R, Module.finrank F (ColDecomp.Icz S c z)) ∧
      ((¬ ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) →
        Module.finrank F ((ColDecomp.idealI S k).map (S.piC c)) = 0) :=
  EvenBlocks.prop65_iii_of_SInv_eq S h c hR
