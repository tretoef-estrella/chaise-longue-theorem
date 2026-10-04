module

public import RequestProject.Pfaffian.Main

/-!
# Part R of `q_rank_two.md`: (R3)

**(R3)** (homogeneity) of Theorem R in `q_rank_two.md`: `pf(t·A) = t^κ·pf(A)` on `Fin (2κ)`, and
`bpf(t·a; c) = t^κ·bpf(a; c)` when `n = s + 2κ`. The first statement by induction with the
recursion of the definition of `pf`; the second from (B5) `Pfaffian.bpf_laplace`.
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian

variable {R : Type*} [CommRing R]

/-- Auxiliary for (R3) of `q_rank_two.md`: a submatrix of `t·A` is `t` times the submatrix. -/
theorem submatrix_smul_aux {m k : ℕ} (t : R) (A : Matrix (Fin m) (Fin m) R) (f g : Fin k → Fin m) :
    (t • A).submatrix f g = t • A.submatrix f g := by
  ext i j; simp

/-- Auxiliary for (R3) of `q_rank_two.md`: `pf(t·A) = t^{⌊m/2⌋}·pf(A)` on `Fin m`, for every
`m` (for odd `m` both sides are `0`). -/
theorem pf_smul_aux : ∀ (m : ℕ) (t : R) (A : Matrix (Fin m) (Fin m) R),
    pf m (t • A) = t ^ (m / 2) * pf m A
  | 0, t, A => by simp
  | 1, t, A => by simp
  | m + 2, t, A => by
    rw [pf_succ_succ, pf_succ_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [submatrix_smul_aux, pf_smul_aux m t, Matrix.smul_apply, smul_eq_mul,
      show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]
    ring

/-- **(R3)** of Theorem R in `q_rank_two.md` (homogeneity), first statement: for every matrix
`A` on `Fin (2κ)` and `t ∈ R`, `pf(t·A) = t^κ·pf(A)`. -/
theorem R3_pf (κ : ℕ) (t : R) (A : Matrix (Fin (2 * κ)) (Fin (2 * κ)) R) :
    pf (2 * κ) (t • A) = t ^ κ * pf (2 * κ) A := by
  rw [pf_smul_aux, show 2 * κ / 2 = κ by omega]

/-- **(R3)** of Theorem R in `q_rank_two.md` (homogeneity), second statement: if `a` is
alternating on `Fin n`, `c` is a list of `s` border columns and `n = s + 2κ`, then
`bpf(t·a; c) = t^κ·bpf(a; c)`. (Proof: from (B5), each term contains `pf` of a restriction of
`t·a` to `n − s = 2κ` indices.) -/
theorem R3_bpf {n s : ℕ} (κ : ℕ) (hn : n = s + 2 * κ) (t : R) (a : Matrix (Fin n) (Fin n) R)
    (ha : IsAlt a) (c : Fin s → Fin n → R) :
    bpf (t • a) c = t ^ κ * bpf a c := by
  have hta : IsAlt (t • a) := ⟨fun i => by simp [ha.1], fun i j => by simp [ha.2 i j]⟩
  rw [bpf_laplace _ hta, bpf_laplace _ ha, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [submatrix_smul_aux, pf_smul_aux, show (n - s) / 2 = κ by omega]
  ring

end RankTwo
