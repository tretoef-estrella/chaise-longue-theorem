import RequestProject.OddLifts.Main

-- Check file for run E12 (q_oddbox_lifts_1.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE12.lean
-- Rule: every hand-restated example carries every type written out.

set_option synthInstance.maxHeartbeats 200000

open Polynomial

#print OddLifts.cleanMBlocks
#print OddLifts.mkMPattern

#check @OddLifts.map_Pfe
#check @OddLifts.mPf_expand
#check @OddLifts.coeff_sign_X_pow_C
#check @OddLifts.Pfe_snoc_eq_zero
#check @OddLifts.Pfe_snoc_top
#check @OddLifts.coeff_mPf_cons
#check @OddLifts.P1
#check @OddLifts.P2
#check @OddLifts.P3
#check @OddLifts.L0a
#check @OddLifts.L0b
#check @OddLifts.orderEmbOfFin_cast
#check @OddLifts.orderEmbOfFin_liftSet
#check @OddLifts.orderEmbOfFin_insert_zero
#check @OddLifts.L1
#check @OddLifts.markedPf_insert_zero
#check @OddLifts.phi_markedPf_insert_zero
#check @OddLifts.card_liftPairs'
#check @OddLifts.disjoint_liftPairs'
#check @OddLifts.prod_liftPairs'
#check @OddLifts.card_cleanMBlocks
#check @OddLifts.disjoint_cleanMBlocks
#check @OddLifts.disjoint_pairs_cleanMBlocks
#check @OddLifts.disjoint_cleanMBlocks_marked
#check @OddLifts.sup_mblocks_eq
#check @OddLifts.cover_cleanMBlocks
#check @OddLifts.prod_cleanMBlocks
#check @OddLifts.prod_mkMPattern
#check @OddLifts.len_eq_of_colLen_one
#check @OddLifts.succ_mem_mcover
#check @OddLifts.exists_mpattern_insert
#check @OddLifts.exists_mpattern_pair
#check @OddLifts.T1
#check @OddLifts.T2
#check @OddLifts.T3
#check @OddLifts.T4
#check @OddLifts.exists_mpattern_zero
#check @OddLifts.prod_eq_Delta_one_mul
#check @OddLifts.mPf_cons_of_eq_zero
#check @OddLifts.T5

#print axioms OddLifts.map_Pfe
#print axioms OddLifts.mPf_expand
#print axioms OddLifts.coeff_sign_X_pow_C
#print axioms OddLifts.Pfe_snoc_eq_zero
#print axioms OddLifts.Pfe_snoc_top
#print axioms OddLifts.coeff_mPf_cons
#print axioms OddLifts.P1
#print axioms OddLifts.P2
#print axioms OddLifts.P3
#print axioms OddLifts.L0a
#print axioms OddLifts.L0b
#print axioms OddLifts.orderEmbOfFin_cast
#print axioms OddLifts.orderEmbOfFin_liftSet
#print axioms OddLifts.orderEmbOfFin_insert_zero
#print axioms OddLifts.L1
#print axioms OddLifts.markedPf_insert_zero
#print axioms OddLifts.phi_markedPf_insert_zero
#print axioms OddLifts.card_liftPairs'
#print axioms OddLifts.disjoint_liftPairs'
#print axioms OddLifts.prod_liftPairs'
#print axioms OddLifts.card_cleanMBlocks
#print axioms OddLifts.disjoint_cleanMBlocks
#print axioms OddLifts.disjoint_pairs_cleanMBlocks
#print axioms OddLifts.disjoint_cleanMBlocks_marked
#print axioms OddLifts.sup_mblocks_eq
#print axioms OddLifts.cover_cleanMBlocks
#print axioms OddLifts.prod_cleanMBlocks
#print axioms OddLifts.prod_mkMPattern
#print axioms OddLifts.len_eq_of_colLen_one
#print axioms OddLifts.succ_mem_mcover
#print axioms OddLifts.exists_mpattern_insert
#print axioms OddLifts.exists_mpattern_pair
#print axioms OddLifts.T1
#print axioms OddLifts.T2
#print axioms OddLifts.T3
#print axioms OddLifts.T4
#print axioms OddLifts.exists_mpattern_zero
#print axioms OddLifts.prod_eq_Delta_one_mul
#print axioms OddLifts.mPf_cons_of_eq_zero
#print axioms OddLifts.T5

-- Hand-restated examples (the statements as the auditor reads them in q_oddbox_lifts_1.md).

-- (P1)
example {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (k : ℕ)
    (hk1 : 2 * h < k + l) (hk2 : l < k + 2) :
    (OddPatterns.mPf h l (Fin.cons (X : R[X]) (fun i : Fin l => (C (w i) : R[X])) :
      Fin (l + 1) → R[X])).coeff k = 0 :=
  OddLifts.P1 h l hl w k hk1 hk2

-- (P2), with the sign (-1)^(l(l+1)/2)
example {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (hlh : l ≤ h) :
    (OddPatterns.mPf h l (Fin.cons (X : R[X]) (fun i : Fin l => (C (w i) : R[X])) :
      Fin (l + 1) → R[X])).coeff (2 * h - l) =
      ((-1 : R) ^ (l * (l + 1) / 2)) * ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, (w j - w i) :=
  OddLifts.P2 h l hl w hlh

-- (P3)
example {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (hlh : l ≤ h) (k : ℕ)
    (hk : 2 * h - l < k) :
    (OddPatterns.mPf h l (Fin.cons (X : R[X]) (fun i : Fin l => (C (w i) : R[X])) :
      Fin (l + 1) → R[X])).coeff k = 0 :=
  OddLifts.P3 h l hl w hlh k hk

-- (L0a), at q = 2h+2
example (F : Type*) [Field F] (h m : ℕ) (hm : 1 ≤ m) (V V' : Ideal (Peel.C F (2 * h + 2) m))
    (hVV' : V ≤ V') (d : ℕ) : Peel.W hm V d ≤ Peel.W hm V' d :=
  OddLifts.L0a hm hVV' d

-- (L0b)
example (F : Type*) [Field F] (h m : ℕ) (Lam : Set OddShapes.Shape) :
    Tight.VLamAll F (2 * h + 2) m (OddShapes.comp Lam false) ≤ OddPatterns.VSAll F h m Lam :=
  OddLifts.L0b h m Lam

-- (L1)
example (F : Type*) [Field F] (h n l : ℕ) (B : Finset (Fin n)) :
    Peel.incl F (2 * h + 2) n (OddPatterns.markedPf F h l B) =
      OddPatterns.markedPf F h l (Lifts.liftSet B) :=
  OddLifts.L1 F h l B

-- (T1)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape)
    (mu lam : ChainLemma.Partition) (hlam : (lam, false) ∈ Lam)
    (T : Tight.TightPattern mu (Finset.univ : Finset (Fin n))) (cs : ℕ) (hcs : 1 ≤ cs)
    (hcol : ∀ c : ℕ, 1 ≤ c → Tight.colLen lam c = Tight.colLen mu c + (if c = cs then 1 else 0))
    (hd : Tight.colLen mu cs ≤ 2 * h) :
    T.prod F (2 * h + 2) ∈
      Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) (Tight.colLen mu cs) :=
  OddLifts.T1 hlam T hcs hcol hd

-- (T2)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape)
    (mu lam : ChainLemma.Partition) (hlam : (lam, false) ∈ Lam)
    (T : Tight.TightPattern mu (Finset.univ : Finset (Fin n))) (c0 : ℕ) (hc0 : 1 ≤ c0)
    (hcol : ∀ c : ℕ, 1 ≤ c → Tight.colLen lam c + (if c = c0 then 1 else 0) = Tight.colLen mu c)
    (hr : 1 ≤ Tight.colLen mu c0) (hrq : Tight.colLen mu c0 ≤ 2 * h + 1) :
    T.prod F (2 * h + 2) ∈
      Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam)
        (2 * h + 1 - Tight.colLen mu c0) :=
  OddLifts.T2 hlam T hc0 hcol hr hrq

-- (T3)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape)
    (mu lam : ChainLemma.Partition) (hlam : (lam, true) ∈ Lam)
    (T : OddPatterns.MarkedPattern mu (Finset.univ : Finset (Fin n))) (cs : ℕ) (hcs : 2 ≤ cs)
    (hcol : ∀ c : ℕ, 1 ≤ c → Tight.colLen lam c = Tight.colLen mu c + (if c = cs then 1 else 0))
    (hd : Tight.colLen mu cs ≤ 2 * h) :
    T.prod F h ∈
      Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) (Tight.colLen mu cs) :=
  OddLifts.T3 hlam T hcs hcol hd

-- (T4)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape)
    (mu lam : ChainLemma.Partition) (hlam : (lam, true) ∈ Lam)
    (T : OddPatterns.MarkedPattern mu (Finset.univ : Finset (Fin n))) (c0 : ℕ) (hc0 : 2 ≤ c0)
    (hcol : ∀ c : ℕ, 1 ≤ c → Tight.colLen lam c + (if c = c0 then 1 else 0) = Tight.colLen mu c)
    (hr : 1 ≤ Tight.colLen mu c0) (hrq : Tight.colLen mu c0 ≤ 2 * h + 1) :
    T.prod F h ∈
      Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam)
        (2 * h + 1 - Tight.colLen mu c0) :=
  OddLifts.T4 hlam T hc0 hcol hr hrq

-- (T5)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape)
    (mu : ChainLemma.Partition) (hmu : (mu, true) ∈ Lam)
    (T : Tight.TightPattern mu (Finset.univ : Finset (Fin n))) (hlen : mu.len ≤ h) :
    T.prod F (2 * h + 2) ∈
      Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) (2 * h - mu.len) :=
  OddLifts.T5 hmu T hlen

-- (L2): the clean marked blocks are the blocks on [2, mu_1] and empty outside
example {k : ℕ} {mu : ChainLemma.Partition} {I : Finset (Fin k)}
    (T : OddPatterns.MarkedPattern mu I) (c : ℕ) :
    OddLifts.cleanMBlocks T c = if c ∈ Finset.Icc 2 (mu.row 1) then T.blocks c else ∅ := rfl
