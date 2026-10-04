module

public import RequestProject.Pfaffian.Perm

/-!
# Part A of `q_pfaffian.md`: (A4), (A3), (A5)

* (A4), the expansion along any index, derived from (A2) and the definition as in the file
  (move `x` to the first place by the cyclic permutation of `0, 1, …, x`);
* (A3), equal rows, over every commutative ring (also when `2 = 0`), with no division by `2`;
* (A5), additivity and homogeneity in the row-and-column of an index.
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv

variable {R : Type*} [CommRing R]

/-- **(A4)** of Theorem A in `q_pfaffian.md`: the sign `ε(x, z) = (−1)^{x+z+1}` if `x < z` and
`ε(x, z) = (−1)^{x+z}` if `z < x` (on the `0`-based values of the indices). -/
def eps (x z : ℕ) : R := if x < z then (-1) ^ (x + z + 1) else (-1) ^ (x + z)

/-- Auxiliary for (A4) of `q_pfaffian.md`: `ε(x, z) = (−1)^{x+z'}` for `z = x.succAbove z'`. -/
theorem eps_succAbove {m : ℕ} (x : Fin (m + 1)) (j : Fin m) :
    (eps (x : ℕ) (x.succAbove j : ℕ) : R) = (-1) ^ ((x : ℕ) + (j : ℕ)) := by
  unfold eps
  rcases lt_or_ge j.castSucc x with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc,
      if_neg (by simp [Fin.lt_def] at h; omega)]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ,
      if_pos (by simp [Fin.le_def] at h; omega)]
    ring

/-- **(A4)** of Theorem A in `q_pfaffian.md` (expansion along any index; property (iii) of the
paper): for an alternating matrix `A` on `Fin (m+2)` and every index `x`,
`pf(A) = Σ_{z ≠ x} ε(x, z)·A(x, z)·pf(A^{x,z})`.
The indices `z ≠ x` are written `z = x.succAbove z'` with `z' : Fin (m+1)`, and the minor
`A^{x,z}` (delete `x` and `z`, keep the order of the others) is the submatrix along
`x.succAbove ∘ z'.succAbove`. -/
theorem pf_expand {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (hA : IsAlt A)
    (x : Fin (m + 2)) :
    pf (m + 2) A = ∑ z : Fin (m + 1), eps (x : ℕ) (x.succAbove z : ℕ) * A x (x.succAbove z) *
      pf m (A.submatrix (fun i => x.succAbove (z.succAbove i))
        (fun i => x.succAbove (z.succAbove i))) := by
  have h := good_all (R := R) (m + 2) x.cycleRange.symm A hA
  rw [Perm.sign_symm, Fin.sign_cycleRange, pf_succ_succ] at h
  push_cast at h
  have hx : ((-1 : R) ^ (x : ℕ)) * (-1) ^ (x : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have e : pf (m + 2) A = (-1) ^ (x : ℕ) * ((-1) ^ (x : ℕ) * pf (m + 2) A) := by
    rw [← mul_assoc, hx, one_mul]
  rw [e, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_def,
    Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ, eps_succAbove, pow_add]
  ring

/-- Auxiliary for (A4) of `q_pfaffian.md`: the range of `x.succAbove ∘ z.succAbove` is the complement of
`{x, x.succAbove z}`. -/
theorem exists_succAbove_succAbove_iff {m : ℕ} (x : Fin (m + 2)) (z : Fin (m + 1))
    (y : Fin (m + 2)) :
    (∃ p, x.succAbove (z.succAbove p) = y) ↔ (y ≠ x ∧ y ≠ x.succAbove z) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Fin.succAbove_ne _ _, fun h => Fin.succAbove_ne _ _ (Fin.succAbove_right_injective h)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨y1, rfl⟩ := Fin.exists_succAbove_eq h1
    have : y1 ≠ z := fun h => h2 (by rw [h])
    obtain ⟨p, rfl⟩ := Fin.exists_succAbove_eq this
    exact ⟨p, rfl⟩

/-- Auxiliary for (A4) of `q_pfaffian.md`: the sum over `z ≠ x` written with `x.succAbove`. -/
theorem sum_erase_eq_sum_succAbove {M : Type*} [AddCommGroup M] {m : ℕ} (x : Fin (m + 1))
    (F : Fin (m + 1) → M) : ∑ z ∈ univ.erase x, F z = ∑ z : Fin m, F (x.succAbove z) := by
  have h1 := Finset.add_sum_erase univ F (mem_univ x)
  have h2 := Fin.sum_univ_succAbove F x
  rw [← h1] at h2
  exact add_left_cancel h2

/-- **(A4)** of Theorem A in `q_pfaffian.md`, in a slightly more general (but equivalent) form,
convenient for Part B: for an alternating matrix `A` on `Fin N` with `N = k + 2` and an index
`x`, `pf(A) = Σ_{z ≠ x} ε(x, z)·A(x, z)·pf(A^{x,z})`, where for each `z ≠ x` the minor `A^{x,z}`
may be computed with *any* increasing enumeration `g z : Fin k → Fin N` of the indices other
than `x` and `z`. -/
theorem pf_expand_gen {N k : ℕ} (hN : N = k + 2) (A : Matrix (Fin N) (Fin N) R) (hA : IsAlt A)
    (x : Fin N) (g : Fin N → Fin k → Fin N)
    (hg : ∀ z, z ≠ x → StrictMono (g z) ∧ ∀ y, (∃ p, g z p = y) ↔ (y ≠ x ∧ y ≠ z)) :
    pf N A = ∑ z ∈ univ.erase x, eps (x : ℕ) (z : ℕ) * A x z * pf k (A.submatrix (g z) (g z)) := by
  subst hN
  rw [pf_expand A hA x, sum_erase_eq_sum_succAbove]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz := hg (x.succAbove z) (Fin.succAbove_ne _ _)
  have e : g (x.succAbove z) = fun i => x.succAbove (z.succAbove i) := by
    refine strictMono_eq_of_range hz.1
      (fun a b h => Fin.strictMono_succAbove _ (Fin.strictMono_succAbove _ h)) fun y => ?_
    rw [hz.2, exists_succAbove_succAbove_iff]
  rw [e]

/-- Auxiliary for (A3) of `q_pfaffian.md`: if the rows `0` and `1` of an alternating matrix are
equal, its Pfaffian is `0` (double expansion: the terms `(j, l)` and `(l, j)` cancel). -/
theorem pf_eq_zero_of_rows01 (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) R) (hB : IsAlt B)
    (h : ∀ k, B 0 k = B 1 k) : pf (m + 2) B = 0 := by
  rcases m with _ | _ | n
  · rw [pf_two, h, hB.1]
  · exact pf_odd 3 _ ⟨1, rfl⟩
  · rw [pf_double, h 1, hB.1, zero_mul, zero_add]
    unfold dT
    simp only [← h]
    rw [← Finset.sum_product' (s := univ) (t := univ)
      (f := fun (j l : Fin (n + 2)) => if j = l then (0 : R) else
        sgn2 j l * B 0 j.succ.succ * B 0 l.succ.succ * pfS n B (dset j l))]
    refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp => ?_)
      (fun p _ => by simp) (fun p _ => by simp)
    · by_cases hjl : p.1 = p.2
      · simp [hjl]
      · simp only [Prod.fst_swap, Prod.snd_swap]
        rw [if_neg hjl, if_neg (Ne.symm hjl), dset_comm p.2 p.1,
          sgn2_swap (fun h => hjl (Fin.ext h))]
        ring
    · intro hs
      apply hp
      have : p.1 = p.2 := by
        have := congrArg Prod.fst hs; simpa using this.symm
      simp [this]

/-- **(A3)** of Theorem A in `q_pfaffian.md` (equal rows; property (ii) of the paper): if `A` is
alternating, `x ≠ z` and `A(x, k) = A(z, k)` for every `k`, then `pf(A) = 0`. This holds over
every commutative ring, also when `2 = 0` (no division by `2` is used: the proof moves `x, z` to
the places `0, 1` by (A2) and cancels the terms of the double expansion in pairs). -/
theorem pf_eq_zero_of_rows {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (hA : IsAlt A)
    {x z : Fin m} (hxz : x ≠ z) (hrow : ∀ k, A x k = A z k) : pf m A = 0 := by
  rcases m with _ | _ | m
  · exact x.elim0
  · exact absurd (Fin.ext (by omega)) hxz
  · set σ : Perm (Fin (m + 2)) := swap 0 x * swap 1 (swap 0 x z) with hσ
    have h01 : (0 : Fin (m + 2)) ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp at this
    have hz0 : swap 0 x z ≠ 0 := by
      intro h
      apply hxz
      have := congrArg (swap 0 x) h
      rw [swap_apply_self, swap_apply_left] at this
      exact this.symm
    have hσ0 : σ 0 = x := by
      simp only [hσ, Perm.coe_mul, Function.comp_apply]
      rw [swap_apply_of_ne_of_ne h01 hz0.symm, swap_apply_left]
    have hσ1 : σ 1 = z := by
      simp only [hσ, Perm.coe_mul, Function.comp_apply, swap_apply_left, swap_apply_self]
    have hB := good_all (R := R) (m + 2) σ A hA
    rw [pf_eq_zero_of_rows01 m _ (hA.submatrix σ) (fun k => by
      simp only [Matrix.submatrix_apply, hσ0, hσ1, hrow])] at hB
    have hu : ((Perm.sign σ : ℤ) : R) * ((Perm.sign σ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    calc pf (m + 2) A = ((Perm.sign σ : ℤ) : R) * (((Perm.sign σ : ℤ) : R) * pf (m + 2) A) := by
          rw [← mul_assoc, hu, one_mul]
      _ = 0 := by rw [← hB, mul_zero]

/-- **(A5)** of Theorem A in `q_pfaffian.md` (additive and homogeneous in the row-and-column of
`x`): let `A, A', A''` be alternating matrices on `Fin m`, equal outside the row and the column
of an index `x` (i.e. at all `(i, j)` with `i ≠ x` and `j ≠ x`), and `λ ∈ R`. If
`A(x, k) = A'(x, k) + λ·A''(x, k)` for every `k`, then `pf(A) = pf(A') + λ·pf(A'')`. -/
theorem pf_add_row {m : ℕ} (A A' A'' : Matrix (Fin m) (Fin m) R) (hA : IsAlt A)
    (hA' : IsAlt A') (hA'' : IsAlt A'') (x : Fin m) (c : R)
    (hout : ∀ i j, i ≠ x → j ≠ x → A' i j = A i j ∧ A'' i j = A i j)
    (hrow : ∀ k, A x k = A' x k + c * A'' x k) :
    pf m A = pf m A' + c * pf m A'' := by
  rcases m with _ | _ | m
  · exact x.elim0
  · simp
  · rw [pf_expand A hA x, pf_expand A' hA' x, pf_expand A'' hA'' x, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e : ∀ B : Matrix (Fin (m + 2)) (Fin (m + 2)) R,
        (∀ i j, i ≠ x → j ≠ x → B i j = A i j) →
        B.submatrix (fun i => x.succAbove (z.succAbove i)) (fun i => x.succAbove (z.succAbove i))
          = A.submatrix (fun i => x.succAbove (z.succAbove i))
            (fun i => x.succAbove (z.succAbove i)) := by
      intro B hB
      ext i j
      exact hB _ _ (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
    rw [e A' (fun i j hi hj => (hout i j hi hj).1), e A'' (fun i j hi hj => (hout i j hi hj).2),
      hrow]
    ring

/-- **(A4)** of Theorem A in `q_pfaffian.md`, in a more general form used for Part B: the
expansion along `x` where the indices `z ≠ x` with `A(x, z) ≠ 0` are listed by an injective
family `φ : ι → Fin N` (the other terms vanish), and each minor `A^{x, φ i}` is computed with any
increasing enumeration `g i` of the indices other than `x` and `φ i`. -/
theorem pf_expand_fam {N k : ℕ} (hN : N = k + 2) (A : Matrix (Fin N) (Fin N) R) (hA : IsAlt A)
    (x : Fin N) {ι : Type*} [Fintype ι] (φ : ι → Fin N) (hφ : Function.Injective φ)
    (hφx : ∀ i, φ i ≠ x) (h0 : ∀ z, z ≠ x → (∀ i, φ i ≠ z) → A x z = 0)
    (g : ι → Fin k → Fin N)
    (hg : ∀ i, StrictMono (g i) ∧ ∀ y, (∃ p, g i p = y) ↔ (y ≠ x ∧ y ≠ φ i)) :
    pf N A = ∑ i, eps (x : ℕ) (φ i : ℕ) * A x (φ i) * pf k (A.submatrix (g i) (g i)) := by
  subst hN
  classical
  rw [pf_expand A hA x]
  set T := univ.filter (fun z' : Fin (k + 1) => ∃ i, φ i = x.succAbove z') with hT
  rw [← Finset.sum_subset (Finset.subset_univ T) ?_]
  · symm
    refine Finset.sum_bij (fun i _ => Classical.choose (Fin.exists_succAbove_eq (hφx i)))
      ?_ ?_ ?_ ?_
    · intro i _
      simp only [hT, mem_filter, mem_univ, true_and]
      exact ⟨i, (Classical.choose_spec (Fin.exists_succAbove_eq (hφx i))).symm⟩
    · intro i _ j _ h
      apply hφ
      rw [← Classical.choose_spec (Fin.exists_succAbove_eq (hφx i)),
        ← Classical.choose_spec (Fin.exists_succAbove_eq (hφx j))]
      exact congrArg x.succAbove h
    · intro z' hz'
      simp only [hT, mem_filter, mem_univ, true_and] at hz'
      obtain ⟨i, hi⟩ := hz'
      refine ⟨i, mem_univ _, ?_⟩
      apply Fin.succAbove_right_injective (p := x)
      rw [Classical.choose_spec (Fin.exists_succAbove_eq (hφx i)), hi]
    · intro i _
      have hz : x.succAbove (Classical.choose (Fin.exists_succAbove_eq (hφx i))) = φ i :=
        Classical.choose_spec (Fin.exists_succAbove_eq (hφx i))
      have e : g i = fun p => x.succAbove
          ((Classical.choose (Fin.exists_succAbove_eq (hφx i))).succAbove p) :=
        strictMono_eq_of_range (hg i).1
          (fun a b h => Fin.strictMono_succAbove _ (Fin.strictMono_succAbove _ h))
          (fun y => by rw [(hg i).2, exists_succAbove_succAbove_iff, hz])
      rw [e, hz]
  · intro z' _ hz'
    simp only [hT, mem_filter, mem_univ, true_and, not_exists] at hz'
    rw [h0 _ (Fin.succAbove_ne _ _) hz', mul_zero, zero_mul]

end Pfaffian
