module

public import RequestProject.Pfaffian.Main

/-!
# Part S of `q_rank_two.md`: definitions, (S0), (S1), (S3)

The **Definitions** of Part S of `q_rank_two.md` (the odd box, `r = 2h + 1`, over a commutative
ring `A`, with `ζ = Polynomial.X` and constants `Polynomial.C`), in the suggested form:
`omega`, the matrices `Wm` (`W_σ(y)`), `Lm` (`L(y)`), `Hm` (`H(y)`) and the columns `Ev`, `Od`.
Then (S0), (S1) and (S3) of Theorem S. `ColOne.Dab` and `Pfaffian.ay` are used unchanged.
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian Polynomial ColOne

variable {A : Type*} [CommRing A]

/-! ### Definitions -/

/-- **Part S, Definitions** of `q_rank_two.md`: `ω_s(a, b) := Σ (−1)^u·a^u·b^{s−u}`, the sum over
the `u` with `0 ≤ u ≤ r − 1` and `0 ≤ s − u ≤ r − 1`. (Here `r` is a parameter; in Part S it is
`2h + 1`.) -/
def omega (r s : ℕ) (a b : A) : A :=
  ∑ u ∈ range r, if u ≤ s ∧ s - u < r then (-1) ^ u * a ^ u * b ^ (s - u) else 0

/-- **Part S, Definitions** of `q_rank_two.md`: the matrix `W_σ(y)` on `Fin n` over `A`, with
entries `ω_{2σ+1}(y_i, y_j)` (`r = 2h + 1`). -/
def Wm (h σ : ℕ) {n : ℕ} (y : Fin n → A) : Matrix (Fin n) (Fin n) A := fun i j =>
  omega (2 * h + 1) (2 * σ + 1) (y i) (y j)

/-- **Part S, Definitions** of `q_rank_two.md`: `L(y) := Σ_{σ=0}^{h−1} ζ^σ·W_σ(y)`, a matrix on
`Fin n` over `A[ζ]`. -/
noncomputable def Lm (h : ℕ) {n : ℕ} (y : Fin n → A) : Matrix (Fin n) (Fin n) A[X] := fun i j =>
  ∑ σ ∈ range h, X ^ σ * C (omega (2 * h + 1) (2 * σ + 1) (y i) (y j))

/-- **Part S, Definitions** of `q_rank_two.md`: `H(y) := Σ_{τ=0}^{h−1} ζ^τ·W_{h+τ}(y)`, a matrix
on `Fin n` over `A[ζ]`. -/
noncomputable def Hm (h : ℕ) {n : ℕ} (y : Fin n → A) : Matrix (Fin n) (Fin n) A[X] := fun i j =>
  ∑ τ ∈ range h, X ^ τ * C (omega (2 * h + 1) (2 * (h + τ) + 1) (y i) (y j))

/-- **Part S, Definitions** of `q_rank_two.md`: the column `Ev(y)_i := Σ_{α=0}^{h} ζ^α·y_i^{2α}`
over `A[ζ]`. -/
noncomputable def Ev (h : ℕ) {n : ℕ} (y : Fin n → A) : Fin n → A[X] := fun i =>
  ∑ α ∈ range (h + 1), X ^ α * C (y i ^ (2 * α))

/-- **Part S, Definitions** of `q_rank_two.md`: the column
`Od(y)_i := Σ_{β=0}^{h−1} ζ^β·y_i^{2β+1}` over `A[ζ]`. -/
noncomputable def Od (h : ℕ) {n : ℕ} (y : Fin n → A) : Fin n → A[X] := fun i =>
  ∑ β ∈ range h, X ^ β * C (y i ^ (2 * β + 1))

/-! ### Coefficients of the sums `Σ ζ^σ·(constant)` -/

/-- Auxiliary for Part S of `q_rank_two.md`: `[ζ^k] Σ_{σ<m} ζ^σ·C(f σ) = f k` if `k < m`, else
`0`. -/
theorem coeff_sum_X_pow_C (m : ℕ) (f : ℕ → A) (k : ℕ) :
    (∑ σ ∈ range m, X ^ σ * C (f σ)).coeff k = if k < m then f k else 0 := by
  rw [finset_sum_coeff]
  simp_rw [mul_comm (X ^ _), C_mul_X_pow_eq_monomial, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_range]

/-- Auxiliary for Part S of `q_rank_two.md`: `Σ_{σ<m} ζ^σ·C(f σ)` has degree at most `m − 1`. -/
theorem natDegree_sum_X_pow_C (m : ℕ) (f : ℕ → A) :
    (∑ σ ∈ range m, X ^ σ * C (f σ)).natDegree ≤ m - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ hσ => ?_
  rw [mul_comm, C_mul_X_pow_eq_monomial]
  exact (natDegree_monomial_le _).trans (by rw [mem_range] at hσ; omega)

/-! ### (S0) -/

/-- Auxiliary for (S0) of `q_rank_two.md`: `ω_s` as a sum over the set of the admissible `u`. -/
theorem omega_eq_sum_filter (r s : ℕ) (a b : A) :
    omega r s a b = ∑ u ∈ (range r).filter (fun u => u ≤ s ∧ s - u < r),
      (-1) ^ u * a ^ u * b ^ (s - u) := by
  rw [omega, Finset.sum_filter]

/-- Auxiliary for (S0) of `q_rank_two.md`: the set of the admissible `u` is stable under
`u ↦ s − u`. -/
theorem mem_filter_sub {r s u : ℕ} (hu : u ∈ (range r).filter (fun u => u ≤ s ∧ s - u < r)) :
    s - u ∈ (range r).filter (fun u => u ≤ s ∧ s - u < r) := by
  simp only [mem_filter, mem_range] at hu ⊢
  omega

/-- Auxiliary for (S0) of `q_rank_two.md`: `(−1)^{s−u} = −(−1)^u` for odd `s` and `u ≤ s`. -/
theorem neg_one_pow_odd_sub {s u : ℕ} (hs : Odd s) (hu : u ≤ s) :
    (-1 : A) ^ (s - u) = -(-1) ^ u := by
  rcases Nat.even_or_odd u with he | ho
  · rw [(Nat.Odd.sub_even hu hs he).neg_one_pow, he.neg_one_pow]
  · rw [(Nat.Odd.sub_odd hs ho).neg_one_pow, ho.neg_one_pow, neg_neg]

/-- **(S0)** of Theorem S in `q_rank_two.md`, first part: for odd `s`,
`ω_s(b, a) = −ω_s(a, b)`. -/
theorem omega_swap (r : ℕ) {s : ℕ} (hs : Odd s) (a b : A) :
    omega r s b a = -omega r s a b := by
  rw [omega_eq_sum_filter, omega_eq_sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun u => s - u) (fun u => s - u) (fun u hu => mem_filter_sub hu)
    (fun u hu => mem_filter_sub hu) (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_)
  · simp only [mem_filter, mem_range] at hu; show s - (s - u) = u; omega
  · simp only [mem_filter, mem_range] at hu; show s - (s - u) = u; omega
  · simp only [mem_filter, mem_range] at hu
    show (-1) ^ u * b ^ u * a ^ (s - u) = -((-1) ^ (s - u) * a ^ (s - u) * b ^ (s - (s - u)))
    rw [show s - (s - u) = u by omega, neg_one_pow_odd_sub hs hu.2.1]
    ring

/-- **(S0)** of Theorem S in `q_rank_two.md`, second part: for odd `s`, `ω_s(a, a) = 0` (the
terms `u` and `s − u` cancel; no division by `2`). -/
theorem omega_self (r : ℕ) {s : ℕ} (hs : Odd s) (a : A) : omega r s a a = 0 := by
  rw [omega_eq_sum_filter]
  refine Finset.sum_involution (fun u _ => s - u) (fun u hu => ?_) (fun u hu _ => ?_)
    (fun u hu => mem_filter_sub hu) (fun u hu => ?_)
  · simp only [mem_filter, mem_range] at hu
    show (-1) ^ u * a ^ u * a ^ (s - u) + (-1) ^ (s - u) * a ^ (s - u) * a ^ (s - (s - u)) = 0
    rw [show s - (s - u) = u by omega, neg_one_pow_odd_sub hs hu.2.1]
    ring
  · obtain ⟨k, rfl⟩ := hs
    show 2 * k + 1 - u ≠ u
    omega
  · simp only [mem_filter, mem_range] at hu; show s - (s - u) = u; omega

/-- **(S0)** of Theorem S in `q_rank_two.md`: `W_σ(y)` is alternating. -/
theorem Wm_isAlt (h σ : ℕ) {n : ℕ} (y : Fin n → A) : IsAlt (Wm h σ y) :=
  ⟨fun _ => omega_self _ ⟨σ, rfl⟩ _, fun _ _ => omega_swap _ ⟨σ, rfl⟩ _ _⟩

/-- **(S0)** of Theorem S in `q_rank_two.md`: `L(y)` is alternating. -/
theorem Lm_isAlt (h : ℕ) {n : ℕ} (y : Fin n → A) : IsAlt (Lm h y) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp [Lm, omega_self _ (⟨_, rfl⟩ : Odd (2 * _ + 1))]
  · simp [Lm, omega_swap _ (⟨_, rfl⟩ : Odd (2 * _ + 1)) (y i) (y j)]

/-- **(S0)** of Theorem S in `q_rank_two.md`: `H(y)` is alternating. -/
theorem Hm_isAlt (h : ℕ) {n : ℕ} (y : Fin n → A) : IsAlt (Hm h y) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp [Hm, omega_self _ (⟨_, rfl⟩ : Odd (2 * _ + 1))]
  · simp [Hm, omega_swap _ (⟨_, rfl⟩ : Odd (2 * _ + 1)) (y i) (y j)]

/-! ### (S1) -/

/-- **(S1)** of Theorem S in `q_rank_two.md`: for `h ≥ 1` and `r = 2h + 1`,
`ω_{r−2}(a, b) = Dab r a b = D^−(a, b)`. -/
theorem S1 {h : ℕ} (hh : 1 ≤ h) (a b : A) :
    omega (2 * h + 1) (2 * h - 1) a b = Dab (2 * h + 1) a b := by
  unfold omega Dab
  rw [Finset.sum_range_succ, if_neg (by omega), add_zero, show 2 * h + 1 - 1 = 2 * h by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [mem_range] at hu
  rw [if_pos (by omega), show 2 * h + 1 - 2 - u = 2 * h - 1 - u by omega]

/-- **(S1)** of Theorem S in `q_rank_two.md`, matrix form: `W_{h−1}(y)` is the matrix `a_y` of
`q_pfaffian.md`, Part C (`Pfaffian.ay (2h+1) y`). -/
theorem S1_Wm {h : ℕ} (hh : 1 ≤ h) {n : ℕ} (y : Fin n → A) :
    Wm h (h - 1) y = ay (2 * h + 1) y := by
  ext i j
  rw [Wm, ay, show 2 * (h - 1) + 1 = 2 * h - 1 by omega, S1 hh]

/-- **(S1)** of Theorem S in `q_rank_two.md`, as used in (S5): the matrix of the top
coefficients `[ζ^{h−1}]` of `L(y)` is `a_y = Pfaffian.ay (2h+1) y`. -/
theorem S1_top {h : ℕ} (hh : 1 ≤ h) {n : ℕ} (y : Fin n → A) :
    (fun i j => (Lm h y i j).coeff (h - 1)) = ay (2 * h + 1) y := by
  rw [← S1_Wm hh]
  ext i j
  rw [Lm, coeff_sum_X_pow_C, if_pos (by omega)]
  rfl

/-- Auxiliary for (S5) of `q_rank_two.md`: the entries of `L(y)` have degree at most `h − 1`. -/
theorem natDegree_Lm (h : ℕ) {n : ℕ} (y : Fin n → A) (i j : Fin n) :
    (Lm h y i j).natDegree ≤ h - 1 :=
  natDegree_sum_X_pow_C h _

/-- Auxiliary for (S5) of `q_rank_two.md`: the entries of `Ev(y)` have degree at most `h`, and
`[ζ^h] Ev(y)_i = y_i^{2h}`. -/
theorem Ev_top (h : ℕ) {n : ℕ} (y : Fin n → A) (i : Fin n) :
    (Ev h y i).natDegree ≤ h ∧ (Ev h y i).coeff h = y i ^ (2 * h) := by
  refine ⟨(natDegree_sum_X_pow_C (h + 1) _).trans (by omega), ?_⟩
  rw [Ev, coeff_sum_X_pow_C, if_pos (by omega)]

/-! ### (S3) -/

/-- **(S3)** of Theorem S in `q_rank_two.md`, in a more general form: for `r = 2h + 1`, every
`i` and `b^r = 0`, `ω_{r−1+i}(a, b) = b^i·Dab (r+1) a b = b^i·D(a, b)`. The hypotheses of the
file that `i` is odd, `1 ≤ i ≤ r − 2` and `a^r = 0` are not needed, so they are omitted (the
statement of the file is the special case). -/
theorem S3 (h i : ℕ) (a b : A) (hb : b ^ (2 * h + 1) = 0) :
    omega (2 * h + 1) (2 * h + i) a b = b ^ i * Dab (2 * h + 2) a b := by
  unfold omega Dab
  rw [Finset.mul_sum, show 2 * h + 2 - 1 = 2 * h + 1 by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [mem_range] at hu
  by_cases hiu : i ≤ u
  · rw [if_pos (by omega), show 2 * h + i - u = i + (2 * h + 2 - 2 - u) by omega, pow_add]
    ring
  · rw [if_neg (by omega), show b ^ (2 * h + 2 - 2 - u) =
      b ^ (2 * h - u) by congr 1, ← mul_assoc, mul_comm (b ^ i), mul_assoc, mul_assoc,
      ← pow_add, show i + (2 * h - u) = (2 * h + 1) + (i - u - 1) by omega, pow_add, hb]
    ring

end RankTwo
