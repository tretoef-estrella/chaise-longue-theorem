import RequestProject.EvenAll.PartBC
import RequestProject.EvenAll.PartD
import RequestProject.EvenAll.PartE

-- Check file for run E20 (q_even_assembly.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE20.lean
-- Imports the four theorem modules directly: EvenAll.Checks (numeric decide checks, no theorems) is
-- killed by the local Lean cap (4.75 GB), so Main (which imports it) is not built locally.
-- Rules: every hand-restated example carries every type written out; every folder cited is
-- imported; `open scoped Classical` as in the files; implicit arguments are not passed.

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColSurv ColComp ColDecomp EvenBlocks EvenColours ColUpper ColAssembly

open scoped Classical

#check @EvenAll.A1
#check @EvenAll.A2
#check @EvenAll.A2_even
#check @EvenAll.A2_odd
#check @EvenAll.A3
#check @EvenAll.B1
#check @EvenAll.B2
#check @EvenAll.Qall
#check @EvenAll.mainTheorem'
#check @EvenAll.D1_NS
#check @EvenAll.D1_Nbal
#check @EvenAll.D2
#check @EvenAll.bip_of_setting
#check @EvenAll.E_prime
#check @EvenAll.E1
#check @EvenAll.E2

#print axioms EvenAll.A1
#print axioms EvenAll.A2
#print axioms EvenAll.A2_even
#print axioms EvenAll.A2_odd
#print axioms EvenAll.A3
#print axioms EvenAll.B1
#print axioms EvenAll.B2
#print axioms EvenAll.mainTheorem'
#print axioms EvenAll.D1_NS
#print axioms EvenAll.D1_Nbal
#print axioms EvenAll.D2
#print axioms EvenAll.bip_of_setting
#print axioms EvenAll.E_prime
#print axioms EvenAll.E1
#print axioms EvenAll.E2

-- (A3) restated: H(m, k) for every even m ≥ 2, every k.
example (m k : ℕ) (heven : Even m) (h2 : 2 ≤ m) : EvenAssembly.HypH m k :=
  EvenAll.A3 heven h2 k

-- (C2) Main Theorem′ restated, every m ≥ 1, every k, every field.
example (m k : ℕ) (hm : 1 ≤ m) :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - EvenAll.Qall m k) ∧
    ∀ (F : Type) [Field F],
      Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - EvenAll.Qall m k ∧
        Module.finrank F ((IK F m k).restrictScalars F) = EvenAll.Qall m k :=
  ⟨(EvenAll.mainTheorem'.{0} hm k).1, fun F _ => (EvenAll.mainTheorem'.{0} hm k).2 F⟩

-- Qall unfolds by parity.
example (m k : ℕ) (h : Even m) : EvenAll.Qall m k = EvenCount.QkEven k m := by
  unfold EvenAll.Qall; rw [if_pos h]

example (m k : ℕ) (h : ¬ Even m) : EvenAll.Qall m k = TheoremB.Qk k m := by
  unfold EvenAll.Qall; rw [if_neg h]

-- (D2) Corollary 9.12 (i) restated.
example (F : Type) [Field F] (S : ColSetting F) (R : Finset F) (hR : EvenBlocks.IsReps2 S R)
    (k : ℕ) (c : Fin (2 * k + 1) → S.μ)
    (hcomp : ∃ J : BallotBound.Matching k, ColComp.Compatible (ColSurv.cExt c) J) :
    (∀ ζ ∈ EvenBlocks.SInv S, Module.finrank F (EvenBlocks.IcS S c ζ) =
        EvenColours.NS S ζ (ColComp.cls (ColSurv.cExt c) ζ).card) ∧
      ∀ ζ ∈ R, Module.finrank F (ColDecomp.Icz S c ζ) =
        Bip.Nbal (ColComp.cls (ColSurv.cExt c) ζ).card S.q :=
  EvenAll.D2 S hR c hcomp

-- (E1) Corollary 9.12 (ii) restated.
example (v a : ℕ) (hv : 1 ≤ v) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Ibal (AlgebraicClosure (ZMod 2)) (2 ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nbal a (2 ^ v) ∧
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Iph (AlgebraicClosure (ZMod 2)) (2 ^ v) a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nph a (2 ^ v) :=
  EvenAll.E1 hv a
