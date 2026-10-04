import RequestProject.OddLayers.Main

-- Check file for run E7 (q_oddbox_layers.md). Grepy Mandalay, 2 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE7.lean

#print OddLayers.layerS
#print OddLayers.toPointed

#check @OddLayers.exchange
#check @OddLayers.FS_le_FS_subE
#check @OddLayers.shape_eq_root_iff
#check @OddLayers.ZS_root_even_eq_closedPointed
#check @OddLayers.card_ZS_root_even
#check @OddLayers.FS_root_even
#check @OddLayers.layerS_root_even_zero
#check @OddLayers.layerS_root_even_pos
#check @OddLayers.card_ZS_root_odd
#check @OddLayers.FS_antitone
#check @OddLayers.isInterlaced_layerS
#check @OddLayers.layerS_succ_subset
#check @OddLayers.layerS_eq_empty
#check @OddLayers.Zgt_ZS_eq_ZS_layerS
#check @OddLayers.card_ZS_eq_sum

#print axioms OddLayers.exchange
#print axioms OddLayers.FS_le_FS_subE
#print axioms OddLayers.shape_eq_root_iff
#print axioms OddLayers.ZS_root_even_eq_closedPointed
#print axioms OddLayers.card_ZS_root_even
#print axioms OddLayers.FS_root_even
#print axioms OddLayers.layerS_root_even_zero
#print axioms OddLayers.layerS_root_even_pos
#print axioms OddLayers.card_ZS_root_odd
#print axioms OddLayers.FS_antitone
#print axioms OddLayers.isInterlaced_layerS
#print axioms OddLayers.layerS_succ_subset
#print axioms OddLayers.layerS_eq_empty
#print axioms OddLayers.Zgt_ZS_eq_ZS_layerS
#print axioms OddLayers.card_ZS_eq_sum

-- The two statements that the next pieces use, restated by hand (they must typecheck as written).
open ChainLemma ChainLemma.Partition Fibres OddShapes OddLayers in
example {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ} (S : OddSetting T h) (k : ℕ) :
    (ZS S (2 * k + 1) {(onePart, false), (emptyPart, true)}).card = EvenCount.QkEven k (2 * h + 2) :=
  card_ZS_root_odd S k

open ChainLemma ChainLemma.Partition Fibres OddShapes OddLayers in
example {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m) {Λ : Set Shape} (hΛ : IsInterlaced h m Λ) (i : ℕ) :
    IsInterlaced h (m - 1) {σ | σ ∈ Sh h (m - 1) ∧ i < FS h Λ σ} :=
  isInterlaced_layerS hh hm hΛ i
