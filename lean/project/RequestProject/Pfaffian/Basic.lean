module

public import Mathlib

/-!
# Part A of `q_pfaffian.md`: definitions and (A0)

This file contains the **Definitions** of Part A of `q_pfaffian.md` (alternating matrices,
minors, the Pfaffian `pf` by recursion on the size) and **(A0)** of Theorem A.

Conventions (as in `q_pfaffian.md`): all indices are `0`-based, `Fin m = {0, …, m−1}`.
Deleting one index `x` of `Fin (m+1)` is `x.succAbove : Fin m → Fin (m+1)` (it keeps the order
of the other indices), and the minor `A^{x}` is `A.submatrix x.succAbove x.succAbove`; the minor
`A^{x,z}` with `z = x.succAbove z'` is `A.submatrix (x.succAbove ∘ z'.succAbove) (…)`.
-/

@[expose] public section

namespace Pfaffian

open Finset

variable {R : Type*} [CommRing R]

/-- **Part A, Definitions** of `q_pfaffian.md`: a matrix `A` on `Fin m` is *alternating* if
`A(i, i) = 0` and `A(j, i) = −A(i, j)` for all `i, j`. (The zero diagonal is asked separately, so
that the notion is the right one also in characteristic `2`.) -/
def IsAlt {m : ℕ} (A : Matrix (Fin m) (Fin m) R) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i j, A j i = -A i j

/-- **Part A, Definitions** of `q_pfaffian.md`: the **Pfaffian** `pf(A)` of a matrix `A` on
`Fin m`, by recursion on `m`: `pf(A) = 1` for `m = 0`, `pf(A) = 0` for `m = 1`, and for `m ≥ 2`
`pf(A) = Σ_{j=1}^{m−1} (−1)^{j+1}·A(0, j)·pf(A^{0,j})`.
Here the sum is written over `j' : Fin (m+1)` with `j = j' + 1` (so the sign `(−1)^{j+1}` is
`(−1)^{j'}`), and the minor `A^{0,j}` is `A.submatrix f f` with `f i = (j'.succAbove i).succ`
(delete the indices `0` and `j`, keep the order of the others). -/
def pf : (m : ℕ) → Matrix (Fin m) (Fin m) R → R
  | 0, _ => 1
  | 1, _ => 0
  | m + 2, A => ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * A 0 j.succ *
      pf m (A.submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ))

/-- The recursion of the definition of `pf` (**Part A, Definitions** of `q_pfaffian.md`). -/
theorem pf_succ_succ (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    pf (m + 2) A = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * A 0 j.succ *
      pf m (A.submatrix (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ)) := rfl

/-- `pf(A) = 1` on `Fin 0` (**Part A, Definitions** of `q_pfaffian.md`). -/
@[simp] theorem pf_zero (A : Matrix (Fin 0) (Fin 0) R) : pf 0 A = 1 := rfl

/-- `pf(A) = 0` on `Fin 1` (**Part A, Definitions** of `q_pfaffian.md`). -/
@[simp] theorem pf_one (A : Matrix (Fin 1) (Fin 1) R) : pf 1 A = 0 := rfl

/-- **Part A, Definitions** of `q_pfaffian.md`: a minor (more generally, any reindexing
`A(f i, f j)`) of an alternating matrix is alternating. -/
theorem IsAlt.submatrix {m k : ℕ} {A : Matrix (Fin m) (Fin m) R} (hA : IsAlt A)
    (f : Fin k → Fin m) : IsAlt (A.submatrix f f) :=
  ⟨fun i => hA.1 (f i), fun i j => hA.2 (f i) (f j)⟩

/-- **(A0)** of Theorem A in `q_pfaffian.md`: `pf(A) = 0` if `m` is odd (for every matrix). -/
theorem pf_odd : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) R), Odd m → pf m A = 0
  | 0, _, h => absurd h (by decide)
  | 1, _, _ => rfl
  | m + 2, A, h => by
    rw [pf_succ_succ]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pf_odd m _ (by rcases h with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩), mul_zero]

/-- **(A0)** of Theorem A in `q_pfaffian.md`, case `m = 2`: `pf(A) = A(0,1)`. -/
theorem pf_two (A : Matrix (Fin 2) (Fin 2) R) : pf 2 A = A 0 1 := by
  simp [pf_succ_succ]

/-- **(A0)** of Theorem A in `q_pfaffian.md`, case `m = 4`:
`pf(A) = A(0,1)A(2,3) − A(0,2)A(1,3) + A(0,3)A(1,2)`. -/
theorem pf_four (A : Matrix (Fin 4) (Fin 4) R) :
    pf 4 A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := by
  simp [pf_succ_succ, Fin.sum_univ_succ]
  ring

end Pfaffian
