module

public import RequestProject.RankTwo.OddDefs

/-!
# Part S of `q_rank_two.md`: (S2), the key fact

**(S2)** of Theorem S in `q_rank_two.md`: in `A[ζ]`,
`Σ_{σ=0}^{2h−1} ζ^σ·ω_{2σ+1}(a, b) = Ev(a)·Od(b) − Ev(b)·Od(a)`, and so, entry by entry,
`L(y) + ζ^h·H(y) = Ev(y)·Od(y)ᵀ − Od(y)·Ev(y)ᵀ`.
The proof is the one of the file: the terms of `ω_{2σ+1}(a, b)` with `u = 2α` even are the terms
`ζ^{α+β} a^{2α} b^{2β+1}` of `Ev(a)·Od(b)`, those with `u = 2β + 1` odd are the terms of
`Ev(b)·Od(a)` with the sign `−`.
-/

@[expose] public section

namespace RankTwo

open Finset Polynomial

variable {A : Type*} [CommRing A]

/-- Auxiliary for (S2) of `q_rank_two.md`: a sum over `u < 2h + 1` split into the even
`u = 2α` (`α ≤ h`) and the odd `u = 2β + 1` (`β < h`). -/
theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (G : ℕ → M) : ∀ h : ℕ,
    ∑ u ∈ range (2 * h + 1), G u =
      ∑ α ∈ range (h + 1), G (2 * α) + ∑ β ∈ range h, G (2 * β + 1)
  | 0 => by simp
  | h + 1 => by
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_even_odd G h, sum_range_succ (fun α => G (2 * α)) (h + 1),
      sum_range_succ (fun β => G (2 * β + 1)) h, show 2 * (h + 1) = 2 * h + 1 + 1 by ring]
    abel

/-- Auxiliary for (S2) of `q_rank_two.md`: the sum over the `σ < N` with `p ≤ σ < p + m` is the
sum over `β < m` of the terms `σ = p + β` (if `p + m ≤ N`). -/
theorem sum_shift_aux {M : Type*} [AddCommMonoid M] (F : ℕ → M) (p m N : ℕ) (h : p + m ≤ N) :
    ∑ σ ∈ range N, (if p ≤ σ ∧ σ - p < m then F σ else 0) = ∑ β ∈ range m, F (p + β) := by
  rw [← Finset.sum_filter]
  have e : (range N).filter (fun σ => p ≤ σ ∧ σ - p < m) = (range m).map (addLeftEmbedding p) := by
    ext σ
    simp only [mem_filter, mem_range, mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨_, h2, h3⟩; exact ⟨σ - p, by omega, by omega⟩
    · rintro ⟨β, hβ, rfl⟩; omega
  rw [e, sum_map]
  rfl

/-- **(S2)** of Theorem S in `q_rank_two.md` (the key fact), for two elements `a, b ∈ A`: in
`A[ζ]`, `Σ_{σ=0}^{2h−1} ζ^σ·ω_{2σ+1}(a, b) = Ev(a)·Od(b) − Ev(b)·Od(a)` with
`Ev(a) = Σ_{α=0}^{h} ζ^α a^{2α}` and `Od(b) = Σ_{β=0}^{h−1} ζ^β b^{2β+1}`. -/
theorem S2_scalar (h : ℕ) (a b : A) :
    ∑ σ ∈ range (2 * h), X ^ σ * C (omega (2 * h + 1) (2 * σ + 1) a b) =
      (∑ α ∈ range (h + 1), X ^ α * C (a ^ (2 * α))) *
          (∑ β ∈ range h, X ^ β * C (b ^ (2 * β + 1))) -
        (∑ α ∈ range (h + 1), X ^ α * C (b ^ (2 * α))) *
          (∑ β ∈ range h, X ^ β * C (a ^ (2 * β + 1))) := by
  -- expand the left side as a double sum and exchange the two sums
  have hL : ∑ σ ∈ range (2 * h), X ^ σ * C (omega (2 * h + 1) (2 * σ + 1) a b) =
      ∑ u ∈ range (2 * h + 1), ∑ σ ∈ range (2 * h),
        (if u ≤ 2 * σ + 1 ∧ 2 * σ + 1 - u < 2 * h + 1 then
          X ^ σ * C ((-1) ^ u * a ^ u * b ^ (2 * σ + 1 - u)) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [omega, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp
  rw [hL, sum_range_even_odd, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := range (h + 1)) (t := range h)
    (f := fun α β => X ^ α * C (b ^ (2 * α)) * (X ^ β * C (a ^ (2 * β + 1)))), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · -- the even `u = 2α`
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [mem_range] at hα
    calc _ = ∑ σ ∈ range (2 * h), (if α ≤ σ ∧ σ - α < h then
            X ^ σ * C (a ^ (2 * α) * b ^ (2 * (σ - α) + 1)) else 0) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          by_cases hc : α ≤ σ ∧ σ - α < h
          · rw [if_pos (by omega), if_pos hc, show 2 * σ + 1 - 2 * α = 2 * (σ - α) + 1 by omega,
              pow_mul, neg_one_sq, one_pow, one_mul]
          · rw [if_neg (by omega), if_neg hc]
      _ = _ := sum_shift_aux _ α h (2 * h) (by omega)
      _ = _ := by
          refine Finset.sum_congr rfl fun β _ => ?_
          dsimp only
          rw [Nat.add_sub_cancel_left, pow_add, map_mul]
          ring
  · -- the odd `u = 2β + 1`
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [mem_range] at hβ
    calc _ = ∑ σ ∈ range (2 * h), (if β ≤ σ ∧ σ - β < h + 1 then
            -(X ^ σ * C (b ^ (2 * (σ - β)) * a ^ (2 * β + 1))) else 0) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          by_cases hc : β ≤ σ ∧ σ - β < h + 1
          · rw [if_pos (by omega), if_pos hc,
              show 2 * σ + 1 - (2 * β + 1) = 2 * (σ - β) by omega,
              pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
            simp only [neg_mul, map_neg, map_mul, map_one]
            ring
          · rw [if_neg (by omega), if_neg hc]
      _ = _ := sum_shift_aux (fun σ => -(X ^ σ * C (b ^ (2 * (σ - β)) * a ^ (2 * β + 1)))) β
          (h + 1) (2 * h) (by omega)
      _ = ∑ α ∈ range (h + 1), -(X ^ α * C (b ^ (2 * α)) * (X ^ β * C (a ^ (2 * β + 1)))) := by
          refine Finset.sum_congr rfl fun α _ => ?_
          dsimp only
          rw [Nat.add_sub_cancel_left, pow_add, map_mul]
          ring
      _ = _ := Finset.sum_neg_distrib _

/-- **(S2)** of Theorem S in `q_rank_two.md` (the key fact), entry by entry:
`L(y)(i, j) + ζ^h·H(y)(i, j) = Ev(y)_i·Od(y)_j − Ev(y)_j·Od(y)_i`. -/
theorem S2 (h : ℕ) {n : ℕ} (y : Fin n → A) (i j : Fin n) :
    Lm h y i j + X ^ h * Hm h y i j = Ev h y i * Od h y j - Ev h y j * Od h y i := by
  rw [Lm, Hm, Ev, Ev, Od, Od, ← S2_scalar, two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [pow_add, mul_assoc, ← two_mul]

end RankTwo
