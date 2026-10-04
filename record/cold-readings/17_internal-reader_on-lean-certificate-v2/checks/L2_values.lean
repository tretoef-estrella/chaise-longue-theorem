import RequestProject.EvenAll.PartBC

-- L2_values.lean — Grepy Sello (cold reader, mission LEAN_2), 4 Oct 2026.
-- Run from material/project:  lake env lean ../../checks/L2_values.lean   (under vigia.sh, Lean cap)
-- 1. finiteness of the integral quotient at m = 6, k = 1 (corrects my failed example of L1);
-- 2. my own Lean count of the set Γ of [DS, Definition 1.3] (no formula), evaluated, against Qall;
-- 3. |Matching k| = (2k+1)!! for k = 0, 1, 2;
-- 4. kernel proofs of Qall at the remaining cells of the mission: (4,1), (4,2), (7,1), (8,1), (9,1).

set_option synthInstance.maxHeartbeats 200000

open ColSplit ColUpper ColAssembly

theorem gs2_Qall61 : EvenAll.Qall 6 1 = 61 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.2.2

-- 1. the integral quotient at (6,1) is a finite free Z-module of rank 155
example : Module.Finite ℤ (RZ 3 6 ⧸ IZ 6 1) ∧ Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by
  have h := (EvenAll.mainTheorem'.{0} (m := 6) (by norm_num) 1).1
  haveI := h.1
  have h155 : Module.finrank ℤ (RZ 3 6 ⧸ IZ 6 1) = 155 := by rw [h.2, gs2_Qall61]
  exact ⟨Module.finite_of_finrank_pos (by rw [h155]; norm_num), h155⟩

-- 2. Γ of [DS, Definition 1.3], written by me: a_i = ζ^{e_i}, e ∈ (Z/m)^{2k+1};
--    a_i ≠ 1  ⇔  e_i ≠ 0;   a_j a_l = 1  ⇔  e_j + e_l ≡ 0 (mod m);  the index 0 never enters.
def gsExt {m k : ℕ} (e : Fin (2 * k + 1) → Fin m) (x : Fin (2 * k + 2)) : ℕ :=
  if h : x.val = 0 then 0 else (e ⟨x.val - 1, by have := x.isLt; omega⟩).val

def gsGamma (m k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * k + 1) → Fin m)).filter (fun e =>
    (∀ i, (e i).val ≠ 0) ∧
    ∃ J : {J : Fin (2 * k + 2) → Fin (2 * k + 2) // ∀ x, J x ≠ x ∧ J (J x) = x},
      ∀ x : Fin (2 * k + 2), (0 < x.val ∧ x < J.1 x) → (gsExt e x + gsExt e (J.1 x)) % m = 0)).card

#eval [gsGamma 3 1, gsGamma 4 1, gsGamma 5 1, gsGamma 6 1, gsGamma 7 1]
#eval [gsGamma 1 0, gsGamma 2 0, gsGamma 5 0, gsGamma 2 1, gsGamma 1 1]
#eval [EvenCount.QkEven 1 4, EvenCount.QkEven 1 6, TheoremB.Qk 1 3, TheoremB.Qk 1 5, TheoremB.Qk 1 7]

-- 3. the index set of the generators has (2k+1)!! elements
example : BallotBound.Matching 2 = {J : Fin 6 → Fin 6 // ∀ x, J x ≠ x ∧ J (J x) = x} := rfl
#eval [Fintype.card {J : Fin 2 → Fin 2 // ∀ x, J x ≠ x ∧ J (J x) = x},
       Fintype.card {J : Fin 4 → Fin 4 // ∀ x, J x ≠ x ∧ J (J x) = x},
       Fintype.card {J : Fin 6 → Fin 6 // ∀ x, J x ≠ x ∧ J (J x) = x}]

-- 4. kernel proofs of Qall (Qall is noncomputable: unfold it, then evaluate in the kernel)
theorem gs2_Qall41 : EvenAll.Qall 4 1 = 19 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.1
theorem gs2_Qall42 : EvenAll.Qall 4 2 = 141 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; exact EvenCount.QkEven_values.2.1
theorem gs2_Qall71 : EvenAll.Qall 7 1 = 90 := by
  unfold EvenAll.Qall; rw [if_neg (by decide)]; decide +kernel
theorem gs2_Qall81 : EvenAll.Qall 8 1 = 127 := by
  unfold EvenAll.Qall; rw [if_pos (by decide)]; decide +kernel
theorem gs2_Qall91 : EvenAll.Qall 9 1 = 168 := by
  unfold EvenAll.Qall; rw [if_neg (by decide)]; decide +kernel

#print axioms gs2_Qall71
#print axioms gs2_Qall81
#print axioms gs2_Qall91
#print axioms gs2_Qall42
