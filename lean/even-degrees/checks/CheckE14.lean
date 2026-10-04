import RequestProject.OddTheorem.Main
import RequestProject.Odd3.Main

-- Check file for run E14 (q_oddbox_theorem.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE14.lean
-- Rule: every hand-restated example carries every type written out.

set_option synthInstance.maxHeartbeats 200000

open ChainLemma ChainLemma.Partition OddShapes Tight OddPatterns

#print OddTheorem.stdOddSetting

#check @OddTheorem.optS_mem_iff
#check @OddTheorem.FS_le
#check @OddTheorem.lemmaK
#check @OddTheorem.P0
#check @OddTheorem.P1
#check @OddTheorem.prop810
#check @OddTheorem.parts_eq_nil_of_mem_Sh_zero
#check @OddTheorem.card_ZS_zero_le
#check @OddTheorem.card_ZS_le_step
#check @OddTheorem.theorem811
#check @OddTheorem.stdOddSetting
#check @OddTheorem.emptyPart_addOne
#check @OddTheorem.marked_emptyPart_mem_DIdeal
#check @OddTheorem.VSAll_root_le_DIdeal
#check @OddTheorem.theoremO

#print axioms OddTheorem.optS_mem_iff
#print axioms OddTheorem.FS_le
#print axioms OddTheorem.lemmaK
#print axioms OddTheorem.P0
#print axioms OddTheorem.P1
#print axioms OddTheorem.prop810
#print axioms OddTheorem.parts_eq_nil_of_mem_Sh_zero
#print axioms OddTheorem.card_ZS_zero_le
#print axioms OddTheorem.card_ZS_le_step
#print axioms OddTheorem.theorem811
#print axioms OddTheorem.stdOddSetting
#print axioms OddTheorem.emptyPart_addOne
#print axioms OddTheorem.marked_emptyPart_mem_DIdeal
#print axioms OddTheorem.VSAll_root_le_DIdeal
#print axioms OddTheorem.theoremO

-- (O) restated by hand: Theorem O (≥), every field, every h ≥ 1, every k.
example (F : Type) [Field F] (h : ℕ) (hh : 1 ≤ h) (k : ℕ) :
    EvenCount.QkEven k (2 * h + 2) ≤
      Module.finrank F ((TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F) :=
  OddTheorem.theoremO F hh k

-- faithfulness point (f): at h = 1 it is exactly Odd3.O_ge_three (degree 4).
example (F : Type) [Field F] (k : ℕ) :
    EvenCount.QkEven k 4 ≤ Module.finrank F ((TheoremB.DIdeal F 4 k).restrictScalars F) :=
  OddTheorem.theoremO F (h := 1) le_rfl k

example (F : Type) [Field F] (k : ℕ) :
    EvenCount.QkEven k 4 ≤ Module.finrank F ((TheoremB.DIdeal F 4 k).restrictScalars F) :=
  Odd3.O_ge_three F k

-- (T) restated by hand.
example (F : Type) [Field F] (T : Type) [Fintype T] [DecidableEq T] (h : ℕ)
    (S : OddSetting T h) (m : ℕ) (Lam : Set Shape) (hΛ : IsInterlaced h m Lam) :
    (ZS S m Lam).card ≤ Module.finrank F ((VSAll F h m Lam).restrictScalars F) :=
  OddTheorem.theorem811 F S m Lam hΛ

-- (P) restated by hand.
example (F : Type) [Field F] (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m) (Lam : Set Shape)
    (hΛ : IsInterlaced h m Lam) (i : ℕ) (hi : i ≤ 2 * h) :
    (VSAll F h (m - 1) (OddLayers.layerS h m Lam i) : Set (Peel.C F (2 * h + 2) (m - 1))) ⊆
      Peel.W hm (VSAll F h m Lam) (2 * h - i) :=
  OddTheorem.prop810 hh hm hΛ hi

-- (P0) restated by hand.
example (F : Type) [Field F] (h : ℕ) (hh : 1 ≤ h) (n : ℕ) (Lam : Set Shape)
    (hΛ : IsInterlaced h (n + 1) Lam) (mu : Partition) (hs : (mu, false) ∈ Sh h n) (i : ℕ)
    (hi : i < FS h Lam (mu, false)) (T : TightPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F (2 * h + 2) ∈
      Peel.W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) :=
  OddTheorem.P0 hh hΛ hs hi T

-- (P1) restated by hand.
example (F : Type) [Field F] (h : ℕ) (hh : 1 ≤ h) (n : ℕ) (Lam : Set Shape)
    (hΛ : IsInterlaced h (n + 1) Lam) (mu : Partition) (hs : (mu, true) ∈ Sh h n) (i : ℕ)
    (hi : i < FS h Lam (mu, true)) (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ Peel.W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) :=
  OddTheorem.P1 hh hΛ hs hi T

-- Lemma K restated by hand (no hypothesis 1 ≤ h: more general, declared by Aristotle).
example (h n : ℕ) (Lam : Set Shape) (hΛ : IsInterlaced h (n + 1) Lam) (mu : Partition) (d : Bool)
    (hs : (mu, d) ∈ Sh h n) (hΦ : 1 ≤ FS h Lam (mu, d)) :
    (∃ lam, (lam, d) ∈ Lam ∧ ∃ cs, (if d then 2 else 1) ≤ cs ∧
        (∀ c, 1 ≤ c → colLen lam c = colLen mu c + if c = cs then 1 else 0) ∧
        colLen mu cs + FS h Lam (mu, d) = 2 * h + 1) ∨
    (d = true ∧ (mu.addOne, true) ∈ Lam ∧ (mu, false) ∈ Lam ∧ mu.len < h ∧
        FS h Lam (mu, d) = 2 * h + 1 - mu.len) ∨
    ((mu, !d) ∈ Lam ∧ FS h Lam (mu, d) = mu.len + 1) ∨
    (∃ lam, (lam, d) ∈ Lam ∧ ∃ c0, (if d then 2 else 1) ≤ c0 ∧
        (∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen mu c) ∧
        colLen mu c0 = FS h Lam (mu, d)) ∨
    (d = true ∧ 1 ≤ mu.len ∧ mu.row mu.len = 1 ∧ (mu.subE mu.len, true) ∈ Lam ∧
        FS h Lam (mu, d) = mu.len) :=
  OddTheorem.lemmaK hΛ hs hΦ

-- the setting of (O): zero is none, the involution flips the Bool.
example (h : ℕ) (hh : 1 ≤ h) : (OddTheorem.stdOddSetting h hh).zero = none := rfl
example (h : ℕ) (hh : 1 ≤ h) (u : Fin h) :
    (OddTheorem.stdOddSetting h hh).neg (some (u, true)) = some (u, false) := rfl
