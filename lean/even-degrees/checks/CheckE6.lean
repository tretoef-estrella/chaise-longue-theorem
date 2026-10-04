import RequestProject.OddShapes.Main

-- Check file for run E6 (q_oddbox_shapes.md). Grepy Mandalay, 2 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE6.lean

#print OddShapes.OddSetting
#print OddShapes.Sh
#print OddShapes.optS
#print OddShapes.FS
#print OddShapes.IsInterlaced

#check @OddShapes.A0
#check @OddShapes.A1
#check @OddShapes.A2_D
#check @OddShapes.A2_Dminus
#check @OddShapes.A3_D
#check @OddShapes.A3_Dminus
#check @OddShapes.A4_D
#check @OddShapes.A4_Dminus
#check @OddShapes.A4_coeff_D
#check @OddShapes.A4_coeff_Dminus
#check @OddShapes.Sh_eq
#check @OddShapes.shape_mem_Sh
#check @OddShapes.shape_consTuple_zero
#check @OddShapes.multiset_shape_consTuple_ne_zero
#check @OddShapes.multiset_shape_consTuple_eq_optS
#check @OddShapes.optS_mem_Sh
#check @OddShapes.FS_eq_card
#check @OddShapes.card_shape_consTuple_mem
#check @OddShapes.card_fiber_ZS
#check @OddShapes.Zgt_ZS
#check @OddShapes.subE_mem_Sh
#check @OddShapes.optS_mem_of_succ
#check @OddShapes.optS_filter_eq_Icc
#check @OddShapes.isInterlaced_empty
#check @OddShapes.isInterlaced_Sh
#check @OddShapes.isInterlaced_root_even
#check @OddShapes.isInterlaced_root_odd

#print axioms OddShapes.A0
#print axioms OddShapes.A1
#print axioms OddShapes.A2_D
#print axioms OddShapes.A2_Dminus
#print axioms OddShapes.A3_D
#print axioms OddShapes.A3_Dminus
#print axioms OddShapes.A4_D
#print axioms OddShapes.A4_Dminus
#print axioms OddShapes.A4_coeff_D
#print axioms OddShapes.A4_coeff_Dminus
#print axioms OddShapes.Sh_eq
#print axioms OddShapes.shape_mem_Sh
#print axioms OddShapes.shape_consTuple_zero
#print axioms OddShapes.multiset_shape_consTuple_ne_zero
#print axioms OddShapes.multiset_shape_consTuple_eq_optS
#print axioms OddShapes.optS_mem_Sh
#print axioms OddShapes.FS_eq_card
#print axioms OddShapes.card_shape_consTuple_mem
#print axioms OddShapes.card_fiber_ZS
#print axioms OddShapes.Zgt_ZS
#print axioms OddShapes.subE_mem_Sh
#print axioms OddShapes.optS_mem_of_succ
#print axioms OddShapes.optS_filter_eq_Icc
#print axioms OddShapes.isInterlaced_empty
#print axioms OddShapes.isInterlaced_Sh
#print axioms OddShapes.isInterlaced_root_even
#print axioms OddShapes.isInterlaced_root_odd

-- My own instances (not Aristotle's), with the numbers written out.
-- (A3) at r = 3 over the integers: (a + b)(b^2 - ab + a^2) = a^3 + b^3.
example (a b : ℤ) : (a + b) * ColOne.Dab 4 a b = a ^ 3 + b ^ 3 :=
  OddShapes.A3_D 3 (by decide) a b
-- (A3) for D^- at r = 5: (a + b) D^-(a,b) = b^4 - a^4.
example (a b : ℤ) : (a + b) * ColOne.Dab 5 a b = b ^ 4 - a ^ 4 :=
  OddShapes.A3_Dminus 5 (by decide) a b
-- (C3) the two roots at h = 2 (r = 5): level 4 (even) and level 3 (odd).
example : OddShapes.IsInterlaced 2 4 {(OddShapes.emptyPart, false)} :=
  OddShapes.isInterlaced_root_even 2 4 (by decide)
example : OddShapes.IsInterlaced 2 3 {(OddShapes.onePart, false), (OddShapes.emptyPart, true)} :=
  OddShapes.isInterlaced_root_odd 2 3 (by decide) (by decide)
-- (C2) for the full set Sh_m at h = 1, m = 2.
-- (first run: this example failed for lack of a Decidable instance for the filter; the axioms had already printed.)
open Classical in
example {μ : ChainLemma.Partition} {δ : Bool} (hs : (μ, δ) ∈ OddShapes.Sh 1 1) :
    (Finset.Icc 1 3).filter (fun p => OddShapes.optS 1 (μ, δ) p ∈ OddShapes.Sh 1 2) =
      Finset.Icc 1 (OddShapes.FS 1 (OddShapes.Sh 1 2) (μ, δ)) :=
  OddShapes.optS_filter_eq_Icc (h := 1) (m := 2) (by decide) (OddShapes.isInterlaced_Sh 1 2) hs
