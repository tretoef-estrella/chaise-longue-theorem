module

public import RequestProject.Pfaffian.Basic

/-!
# Part A of `q_pfaffian.md`: (A2) simultaneous permutations

Proof of (A2) of Theorem A, following the structure of the file: by induction on the size,
using the expansion along the index `0` (the definition) and the double expansion for the
exchange of the indices `0` and `1`.
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv

variable {R : Type*} [CommRing R]

/-- Two strictly monotone maps `Fin k → Fin N` with the same range are equal (auxiliary for
Part A of `q_pfaffian.md`: a minor depends only on the set of kept indices). -/
theorem strictMono_eq_of_range {k N : ℕ} {f g : Fin k → Fin N} (hf : StrictMono f)
    (hg : StrictMono g) (h : ∀ y, (∃ x, f x = y) ↔ (∃ x, g x = y)) : f = g :=
  (hf.range_inj hg).1 (Set.ext fun y => h y)

/-- Auxiliary for Part A of `q_pfaffian.md`: the Pfaffian of the minor of `A` kept on a set `S`
of `n` indices (in increasing order); `0` if `S` does not have `n` elements. -/
noncomputable def pfS {N : ℕ} (n : ℕ) (A : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N)) : R :=
  if h : S.card = n then pf n (A.submatrix (S.orderEmbOfFin h) (S.orderEmbOfFin h)) else 0

/-- Auxiliary for Part A of `q_pfaffian.md`: `pfS` computed with any increasing enumeration of
the set `S`. -/
theorem pfS_eq {N n : ℕ} (A : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (f : Fin n → Fin N) (hf : StrictMono f) (hS : ∀ y, y ∈ S ↔ ∃ x, f x = y) :
    pfS n A S = pf n (A.submatrix f f) := by
  have hc : S.card = n := by
    have : S = Finset.univ.image f := by ext y; simp [hS]
    rw [this, Finset.card_image_of_injective _ hf.injective]; simp
  unfold pfS; rw [dif_pos hc]
  have := Finset.orderEmbOfFin_unique hc (f := f) (fun x => (hS _).2 ⟨x, rfl⟩) hf
  rw [← this]

/-- Auxiliary for Part A of `q_pfaffian.md`: a permutation fixing the kept indices does not
change the minor. -/
theorem pfS_submatrix_of_fix {N n : ℕ} (A : Matrix (Fin N) (Fin N) R) (σ : Perm (Fin N))
    (S : Finset (Fin N)) (h : ∀ y ∈ S, σ y = y) :
    pfS n (A.submatrix σ σ) S = pfS n A S := by
  unfold pfS; split_ifs with hc
  · congr 1; ext i j; simp [h _ (Finset.orderEmbOfFin_mem _ _ _)]
  · rfl

/-- Auxiliary for (A2) of `q_pfaffian.md`: the permutation `σ` satisfies (A2) for all
alternating matrices of size `m`. -/
def Good (R : Type*) [CommRing R] (m : ℕ) (σ : Perm (Fin m)) : Prop :=
  ∀ A : Matrix (Fin m) (Fin m) R, IsAlt A →
    pf m (A.submatrix σ σ) = ((Perm.sign σ : ℤ) : R) * pf m A

/-- Auxiliary for (A2) of `q_pfaffian.md`: the permutations satisfying (A2) are closed under products. -/
theorem Good.mul {m : ℕ} {σ τ : Perm (Fin m)} (hσ : Good R m σ) (hτ : Good R m τ) :
    Good R m (σ * τ) := by
  intro A hA
  have e : A.submatrix (σ * τ : Perm (Fin m)) (σ * τ : Perm (Fin m)) =
      (A.submatrix σ σ).submatrix τ τ := by
    ext i j; simp
  rw [e, hτ _ (hA.submatrix _), hσ A hA, Perm.sign_mul]
  push_cast; ring

/-- Auxiliary for (A2) of `q_pfaffian.md`: a permutation `ρ` of `Fin (m+1)` and an index `p`
induce a permutation `π` of `Fin m` on the complements, with `sgn π = sgn ρ · (−1)^{p + ρ p}`. -/
theorem induced_perm {m : ℕ} (ρ : Perm (Fin (m + 1))) (p : Fin (m + 1)) :
    ∃ π : Perm (Fin m), (∀ i, ρ (p.succAbove i) = (ρ p).succAbove (π i)) ∧
      ((Perm.sign π : ℤ) : R) = ((Perm.sign ρ : ℤ) : R) * (-1) ^ ((p : ℕ) + (ρ p : ℕ)) := by
  set μ : Perm (Fin (m + 1)) := (ρ p).cycleRange * ρ * p.cycleRange.symm with hμ
  obtain ⟨⟨q, π⟩, hqπ⟩ := Perm.decomposeFin.symm.surjective μ
  have hq : q = 0 := by
    have h0 := Perm.decomposeFin_symm_apply_zero q π
    rw [hqπ] at h0
    rw [← h0, hμ]; simp [Fin.cycleRange_symm_zero, Fin.cycleRange_self]
  subst hq
  refine ⟨π, fun i => ?_, ?_⟩
  · have h1 := Perm.decomposeFin_symm_apply_succ π 0 i
    rw [hqπ, hμ] at h1
    simp only [Perm.coe_mul, Function.comp_apply, Fin.cycleRange_symm_succ, swap_self,
      Equiv.refl_apply] at h1
    rw [← Fin.cycleRange_symm_succ (ρ p) (π i), ← h1]; simp
  · have h2 := Perm.decomposeFin.symm_sign (0 : Fin (m + 1)) π
    rw [hqπ, hμ] at h2
    simp only [Perm.sign_mul, Perm.sign_symm, Fin.sign_cycleRange, if_true, one_mul] at h2
    rw [← h2]; push_cast; ring_nf

/-- Auxiliary for (A2) of `q_pfaffian.md` (the case `k ≥ 1` of the file, in the form: every
permutation fixing the index `0`): if (A2) holds in size `m`, then it holds in size `m + 2` for
the permutations fixing `0`. -/
theorem good_of_fix_zero {m : ℕ} (ih : ∀ σ, Good R m σ) (σ : Perm (Fin (m + 2)))
    (h0 : σ 0 = 0) : Good R (m + 2) σ := by
  intro A hA
  obtain ⟨ρ, hρ, hsρ⟩ := induced_perm (R := R) σ 0
  simp only [Fin.succAbove_zero, h0, Fin.val_zero, add_zero, pow_zero, mul_one] at hρ hsρ
  have key : ∀ j : Fin (m + 1),
      pf m ((A.submatrix σ σ).submatrix (fun i => (j.succAbove i).succ)
        (fun i => (j.succAbove i).succ)) =
      ((Perm.sign ρ : ℤ) : R) * (-1) ^ ((j : ℕ) + (ρ j : ℕ)) *
        pf m (A.submatrix (fun i => ((ρ j).succAbove i).succ)
          (fun i => ((ρ j).succAbove i).succ)) := by
    intro j
    obtain ⟨π, hπ, hsπ⟩ := induced_perm (R := R) ρ j
    have e : (A.submatrix σ σ).submatrix (fun i => (j.succAbove i).succ)
        (fun i => (j.succAbove i).succ) =
        (A.submatrix (fun i => ((ρ j).succAbove i).succ)
          (fun i => ((ρ j).succAbove i).succ)).submatrix π π := by
      ext a b; simp [hρ, hπ]
    rw [e, ih π _ (hA.submatrix _), hsπ]
  rw [pf_succ_succ, pf_succ_succ, ← hsρ, Finset.mul_sum]
  refine Fintype.sum_equiv ρ _ _ fun j => ?_
  rw [key]
  simp only [Matrix.submatrix_apply, h0, hρ]
  rw [pow_add]
  have h2 : ((-1 : R) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((Perm.sign ρ : ℤ) : R) * (-1) ^ (ρ j : ℕ) * A 0 (ρ j).succ *
    pf m (A.submatrix (fun i => ((ρ j).succAbove i).succ) (fun i => ((ρ j).succAbove i).succ)) * h2

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: the sign `s(j, l)` of the double expansion
(indices shifted by `2`). -/
def sgn2 (j l : ℕ) : R := if l < j then (-1) ^ (j + l + 1) else (-1) ^ (j + l)

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: `s(l, j) = −s(j, l)`. -/
theorem sgn2_swap {j l : ℕ} (h : j ≠ l) : (sgn2 l j : R) = -sgn2 j l := by
  unfold sgn2
  rcases lt_or_gt_of_ne h with h | h
  · rw [if_pos h, if_neg (by omega), add_comm l j]; ring
  · rw [if_neg (by omega), if_pos h, add_comm l j]; ring

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: `s(j, l) = (−1)^{j+1}·(−1)^{l'}` where `l'` is the position of `l` in the minor. -/
theorem sgn2_succAbove {n : ℕ} (i : Fin (n + 1)) (l : Fin n) :
    (sgn2 (i : ℕ) (i.succAbove l : ℕ) : R) = (-1) ^ ((i : ℕ) + 1) * (-1) ^ (l : ℕ) := by
  unfold sgn2
  rcases lt_or_ge l.castSucc i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc, if_pos (by simpa [Fin.lt_def] using h)]
    ring
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ,
      if_neg (by simp [Fin.le_def] at h; omega)]
    ring

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: the set of indices kept in the double expansion. -/
def dset {n : ℕ} (j l : Fin (n + 2)) : Finset (Fin (n + 4)) :=
  univ.filter (fun y => y ≠ 0 ∧ y ≠ 1 ∧ y ≠ j.succ.succ ∧ y ≠ l.succ.succ)

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: the kept set is symmetric in `j, l`. -/
theorem dset_comm {n : ℕ} (j l : Fin (n + 2)) : dset j l = dset l j := by
  ext; simp [dset]; tauto

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md`: the double sum of the double expansion
`Σ_{j ≠ l, j, l ≥ 2} s(j, l)·A(0, j)·A(1, l)·pf(A^{0,1,j,l})`. -/
noncomputable def dT (n : ℕ) (A : Matrix (Fin (n + 4)) (Fin (n + 4)) R) : R :=
  ∑ j : Fin (n + 2), ∑ l : Fin (n + 2), if j = l then 0 else
    sgn2 j l * A 0 j.succ.succ * A 1 l.succ.succ * pfS n A (dset j l)

/-- Auxiliary for (A2)/(A3) of `q_pfaffian.md` (proof of (A2), case `k = 0`): the double
expansion `pf(A) = A(0,1)·pf(A^{0,1}) + Σ_{j ≠ l} s(j, l)·A(0, j)·A(1, l)·pf(A^{0,1,j,l})`. -/
theorem pf_double (n : ℕ) (A : Matrix (Fin (n + 4)) (Fin (n + 4)) R) :
    pf (n + 4) A = A 0 1 * pf (n + 2) (A.submatrix (fun i => i.succ.succ) (fun i => i.succ.succ))
      + dT n A := by
  rw [pf_succ_succ, Fin.sum_univ_succ]
  congr 1
  · simp
  · unfold dT
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pf_succ_succ, Finset.mul_sum, Fin.sum_univ_succAbove _ i, if_pos rfl, zero_add]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [if_neg (Fin.succAbove_ne i l).symm]
    have hP : pfS n A (dset i (i.succAbove l)) =
        pf n ((A.submatrix (fun q => (i.succ.succAbove q).succ)
          (fun q => (i.succ.succAbove q).succ)).submatrix
          (fun q => (l.succAbove q).succ) (fun q => (l.succAbove q).succ)) := by
      rw [Matrix.submatrix_submatrix]
      have e : ((fun q => (i.succ.succAbove q).succ) ∘ fun q => (l.succAbove q).succ) =
          fun q => (i.succAbove (l.succAbove q)).succ.succ := by
        funext q; simp [Fin.succ_succAbove_succ]
      rw [e]
      apply pfS_eq
      · intro a b h
        simp only [Fin.succ_lt_succ_iff]
        exact Fin.strictMono_succAbove _ (Fin.strictMono_succAbove _ h)
      · intro y
        simp only [dset, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h0, h1, hj, hl⟩
          obtain ⟨y1, rfl⟩ := Fin.exists_succ_eq.2 h0
          have hy1 : y1 ≠ 0 := fun h => h1 (by rw [h, Fin.succ_zero_eq_one])
          obtain ⟨y2, rfl⟩ := Fin.exists_succ_eq.2 hy1
          have hj' : y2 ≠ i := fun h => hj (by rw [h])
          obtain ⟨y3, rfl⟩ := Fin.exists_succAbove_eq hj'
          have hl' : y3 ≠ l := fun h => hl (by rw [h])
          obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hl'
          exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          refine ⟨Fin.succ_ne_zero _, fun h => ?_, fun h => ?_, fun h => ?_⟩
          · rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          · exact Fin.succAbove_ne _ _ (Fin.succ_injective _ (Fin.succ_injective _ h))
          · exact Fin.succAbove_ne _ _ (Fin.succAbove_right_injective
              (Fin.succ_injective _ (Fin.succ_injective _ h)))
    rw [hP, sgn2_succAbove]
    simp only [Matrix.submatrix_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
      Fin.val_succ, Fin.succ_zero_eq_one]
    ring

/-- Auxiliary for (A2) of `q_pfaffian.md`, case `k = 0` of the file: exchanging the indices `0`
and `1` changes the sign of the Pfaffian (via the double expansion). -/
theorem good_swap01 (m : ℕ) : Good R (m + 2) (swap 0 1) := by
  intro A hA
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; simp at this
  rw [Perm.sign_swap h01]
  rcases m with _ | _ | n
  · simp [pf_two, swap_apply_left, hA.2 0 1]
  · rw [pf_odd 3 _ ⟨1, rfl⟩, pf_odd 3 _ ⟨1, rfl⟩]; simp
  · rw [pf_double, pf_double]
    have hfix : ∀ j : Fin (n + 2), swap (0 : Fin (n + 4)) 1 j.succ.succ = j.succ.succ := by
      intro j
      refine swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) fun h => ?_
      rw [← Fin.succ_zero_eq_one] at h
      exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
    have hsub : (A.submatrix (swap (0 : Fin (n + 4)) 1) (swap 0 1)).submatrix
        (fun i : Fin (n + 2) => i.succ.succ) (fun i : Fin (n + 2) => i.succ.succ) =
        A.submatrix (fun i : Fin (n + 2) => i.succ.succ) (fun i : Fin (n + 2) => i.succ.succ) := by
      ext a b; simp [hfix]
    have hT : dT n (A.submatrix (swap (0 : Fin (n + 4)) 1) (swap 0 1)) = -dT n A := by
      unfold dT
      conv_rhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases hjl : j = l
      · simp [hjl]
      · rw [if_neg hjl, if_neg (Ne.symm hjl), pfS_submatrix_of_fix, dset_comm l j,
          sgn2_swap (fun h => hjl (Fin.ext h))]
        · simp only [Matrix.submatrix_apply, hfix, swap_apply_left]
          rw [swap_apply_right]; ring
        · intro y hy
          simp only [dset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          exact swap_apply_of_ne_of_ne hy.1 hy.2.1
    rw [hsub, hT]
    simp [swap_apply_left, swap_apply_right, hA.2 0 1]
    ring

/-- Auxiliary for (A2) of `q_pfaffian.md`: every permutation satisfies (A2), by induction on
the size (`m → m + 2`), writing a permutation as a product of permutations fixing `0` and of
the transposition `(0 1)`. -/
theorem good_all : ∀ (m : ℕ) (σ : Perm (Fin m)), Good R m σ
  | 0, σ => by
    intro A _
    rw [Subsingleton.elim σ 1]; simp
  | 1, σ => by intro A _; simp
  | m + 2, σ => by
    have ih := good_all m
    by_cases h0 : σ 0 = 0
    · exact good_of_fix_zero ih σ h0
    · have h01 : (0 : Fin (m + 2)) ≠ 1 := by
        intro h; have := congrArg Fin.val h; simp at this
      set τ : Perm (Fin (m + 2)) := swap 1 (σ 0) with hτ
      have hτ0 : τ 0 = 0 := swap_apply_of_ne_of_ne h01 (Ne.symm h0)
      set ν : Perm (Fin (m + 2)) := swap 0 1 * τ * σ with hν
      have hν0 : ν 0 = 0 := by
        simp only [hν, Perm.coe_mul, Function.comp_apply, hτ, swap_apply_right,
          swap_apply_right]
      have e : σ = τ * (swap 0 1 * ν) := by
        simp only [hν, hτ, mul_assoc, swap_mul_self_mul]
      rw [e]
      exact (good_of_fix_zero ih τ hτ0).mul ((good_swap01 m).mul (good_of_fix_zero ih ν hν0))

/-- **(A2)** of Theorem A in `q_pfaffian.md` (simultaneous permutation; property (i) of the
paper): for an alternating matrix `A` on `Fin m` and every permutation `σ` of `Fin m`, the
matrix `A^σ(i, j) := A(σ i, σ j)` is alternating and `pf(A^σ) = sgn(σ)·pf(A)`. -/
theorem pf_perm {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (hA : IsAlt A) (σ : Perm (Fin m)) :
    IsAlt (A.submatrix σ σ) ∧ pf m (A.submatrix σ σ) = ((Perm.sign σ : ℤ) : R) * pf m A :=
  ⟨hA.submatrix _, good_all m σ A hA⟩

end Pfaffian
