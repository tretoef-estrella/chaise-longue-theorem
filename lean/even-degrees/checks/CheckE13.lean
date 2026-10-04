import RequestProject.OddLifts2.Main

-- Check file for run E13 (q_oddbox_lifts_2.md). Grepy Mandalay, 3 Oct 2026.
-- Run from proyecto_lean/output-final_aristotle:  lake env lean ../../checks/CheckE13.lean
-- Rule: every hand-restated example carries every type written out.

set_option synthInstance.maxHeartbeats 200000

open Polynomial

#print OddLifts2.Phi
#print OddLifts2.Psi

#check @OddLifts2.Pfe_cons_expand
#check @OddLifts2.Pfe_cons_expand_zero
#check @OddLifts2.Pf_C_snoc_pow
#check @OddLifts2.coeff_Pf_Dminus
#check @OddLifts2.mPf_succ_eq
#check @OddLifts2.mPf_zero_eq
#check @OddLifts2.coeff_Pfe_cons
#check @OddLifts2.coeff_Pfe_cons_zero
#check @OddLifts2.snoc_range_eq
#check @OddLifts2.Q1
#check @OddLifts2.Q2
#check @OddLifts2.Phi
#check @OddLifts2.Pf_D_eq
#check @OddLifts2.Phi_zero
#check @OddLifts2.Phi_succ
#check @OddLifts2.Q'1
#check @OddLifts2.Q'2
#check @OddLifts2.colLen_addOne'
#check @OddLifts2.subset_sup_of_mem
#check @OddLifts2.exists_tpattern_addOne
#check @OddLifts2.disjoint_liftSet_pair_Z
#check @OddLifts2.disjoint_liftSet_block_Z
#check @OddLifts2.mem_cover_lift
#check @OddLifts2.exists_mpattern_lift
#check @OddLifts2.exists_tpattern_lift
#check @OddLifts2.map_Pf
#check @OddLifts2.orderEmbOfFin_erase
#check @OddLifts2.markedPf_erase
#check @OddLifts2.markedPf_eq_Delta
#check @OddLifts2.Psi
#check @OddLifts2.phi_Psi
#check @OddLifts2.Psi_mem
#check @OddLifts2.prod_eq_markedPf_mul
#check @OddLifts2.T6
#check @OddLifts2.colLen_subE_len_of_two_le
#check @OddLifts2.len_subE_len
#check @OddLifts2.T8
#check @OddLifts2.T7

#print axioms OddLifts2.Pfe_cons_expand
#print axioms OddLifts2.Pfe_cons_expand_zero
#print axioms OddLifts2.Pf_C_snoc_pow
#print axioms OddLifts2.coeff_Pf_Dminus
#print axioms OddLifts2.mPf_succ_eq
#print axioms OddLifts2.mPf_zero_eq
#print axioms OddLifts2.coeff_Pfe_cons
#print axioms OddLifts2.coeff_Pfe_cons_zero
#print axioms OddLifts2.snoc_range_eq
#print axioms OddLifts2.Q1
#print axioms OddLifts2.Q2
#print axioms OddLifts2.Phi
#print axioms OddLifts2.Pf_D_eq
#print axioms OddLifts2.Phi_zero
#print axioms OddLifts2.Phi_succ
#print axioms OddLifts2.Q'1
#print axioms OddLifts2.Q'2
#print axioms OddLifts2.colLen_addOne'
#print axioms OddLifts2.subset_sup_of_mem
#print axioms OddLifts2.exists_tpattern_addOne
#print axioms OddLifts2.disjoint_liftSet_pair_Z
#print axioms OddLifts2.disjoint_liftSet_block_Z
#print axioms OddLifts2.mem_cover_lift
#print axioms OddLifts2.exists_mpattern_lift
#print axioms OddLifts2.exists_tpattern_lift
#print axioms OddLifts2.map_Pf
#print axioms OddLifts2.orderEmbOfFin_erase
#print axioms OddLifts2.markedPf_erase
#print axioms OddLifts2.markedPf_eq_Delta
#print axioms OddLifts2.Psi
#print axioms OddLifts2.phi_Psi
#print axioms OddLifts2.Psi_mem
#print axioms OddLifts2.prod_eq_markedPf_mul
#print axioms OddLifts2.T6
#print axioms OddLifts2.colLen_subE_len_of_two_le
#print axioms OddLifts2.len_subE_len
#print axioms OddLifts2.T8
#print axioms OddLifts2.T7

-- Hand-restated examples (the statements as the auditor reads them in q_oddbox_lifts_2.md).

-- Lemma Q, (Q1)
example {R : Type*} [CommRing R] (h l n t : ℕ) (hn : n = l + 2 + 2 * t) (hlh : l + 1 ≤ h)
    (w : Fin n → R) (k : ℕ) (hk : 2 * h - l < k) :
    (OddPatterns.mPf h l (Fin.cons Polynomial.X (fun i => Polynomial.C (w i)) :
      Fin (n + 1) → Polynomial R)).coeff k = 0 :=
  OddLifts2.Q1 h l n t hn hlh w k hk

-- Lemma Q, (Q2)
example {R : Type*} [CommRing R] (h l n t : ℕ) (hn : n = l + 2 + 2 * t) (hlh : l + 1 ≤ h)
    (w : Fin n → R) :
    (OddPatterns.mPf h l (Fin.cons Polynomial.X (fun i => Polynomial.C (w i)) :
      Fin (n + 1) → Polynomial R)).coeff (2 * h - l) = (-1) ^ l * OddPatterns.mPf h (l + 1) w :=
  OddLifts2.Q2 h l n t hn hlh w

-- Phi unfolded, as in the instruction
example {R : Type*} [CommRing R] (h ell n : ℕ) (w : Fin n → R) :
    OddLifts2.Phi h ell w =
      Polynomial.X * OddPatterns.mPf h (ell + 1)
          (Fin.cons Polynomial.X (fun i => Polynomial.C (w i)) : Fin (n + 1) → Polynomial R) +
        Pfaffian.Pf (2 * h + 1) (fun i => Polynomial.C (w i))
          (Fin.snoc (α := fun _ => Fin n → Polynomial R)
            (fun (k : Fin ell) i => (Polynomial.C (w i)) ^ (k : ℕ))
            (fun b => ColOne.Dab (2 * h + 2) Polynomial.X (Polynomial.C (w b)))) := rfl

-- Lemma Q', (Q'1) and (Q'2)
example {R : Type*} [CommRing R] (h ell n t : ℕ) (hn : n = ell + 1 + 2 * t) (w : Fin n → R)
    (k : ℕ) (hk : ell < k) : (OddLifts2.Phi h ell w).coeff k = 0 :=
  OddLifts2.Q'1 h ell n t hn w k hk

example {R : Type*} [CommRing R] (h ell n t : ℕ) (hn : n = ell + 1 + 2 * t) (w : Fin n → R) :
    (OddLifts2.Phi h ell w).coeff ell = OddPatterns.mPf h ell w :=
  OddLifts2.Q'2 h ell n t hn w

-- (T6)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape) (mu : ChainLemma.Partition)
    (hmu : (mu, false) ∈ Lam) (hh : 1 ≤ h) (hlen : mu.len ≤ h)
    (T : OddPatterns.MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) (2 * h - mu.len) :=
  OddLifts2.T6 hmu hh hlen T

-- (T7)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape) (mu : ChainLemma.Partition)
    (hlam : (mu.addOne, true) ∈ Lam) (hmu : (mu, false) ∈ Lam) (hlen : mu.len < h)
    (T : OddPatterns.MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) mu.len :=
  OddLifts2.T7 hlam hmu hlen T

-- (T8)
example (F : Type*) [Field F] (h n : ℕ) (Lam : Set OddShapes.Shape) (mu : ChainLemma.Partition)
    (hlam : (mu.subE mu.len, true) ∈ Lam) (hl1 : 1 ≤ mu.len) (hlh : mu.len ≤ h)
    (hrow : mu.row mu.len = 1) (T : OddPatterns.MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ Peel.W (m := n + 1) (by omega) (OddPatterns.VSAll F h (n + 1) Lam) (2 * h + 1 - mu.len) :=
  OddLifts2.T8 hlam hl1 hlh hrow T
