module

public import RequestProject.ColOne.Sum

/-!
# Part A of `q_oddbox_shapes.md`: elementary identities

This file formalizes **Part A** ("Elementary identities") of `q_oddbox_shapes.md`, items
(A0)–(A4). Throughout, `A` is an arbitrary commutative ring, `a b : A`, and
`D(a, b) = ColOne.Dab (r + 1) a b`, `D^−(a, b) = ColOne.Dab r a b`, where
`ColOne.Dab q a b = Σ_{u=0}^{q−2} (−1)^u a^u b^{q−2−u}` is the divided difference of
`q_col_one.md` (used unchanged).
-/

@[expose] public section

namespace OddShapes

open ColOne

variable {A : Type*} [CommRing A]

/-- **(A0)** of `q_oddbox_shapes.md` (Part A, every `r`, no parity):
`(a + b)·Dab q a b = b^{q−1} − (−a)^{q−1}`.
The file states it for `q ≥ 1`; it also holds for `q = 0` (both sides are `0`), so it is stated
here for every natural number `q` (a slightly more general statement). -/
theorem A0 (q : ℕ) (a b : A) : (a + b) * Dab q a b = b ^ (q - 1) - (-a) ^ (q - 1) := by
  have h := geom_sum₂_mul (-a) b (q - 1)
  have e : Dab q a b = ∑ i ∈ Finset.range (q - 1), (-a) ^ i * b ^ (q - 1 - 1 - i) := by
    unfold Dab
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [neg_pow a, show q - 2 - u = q - 1 - 1 - u by omega]
  rw [e]
  linear_combination (-1 : A) * h

/-- **(A1)** of `q_oddbox_shapes.md` (Part A, every `r ≥ 1`, no parity):
`D(a, b) = b^{r−1} − a·D^−(a, b)`, i.e. `Dab (r+1) a b = b^{r−1} − a·Dab r a b`.
(The hypothesis `r ≥ 1` of the file is needed: for `r = 0` the left side is `0` and the right
side is `1`.) -/
theorem A1 (r : ℕ) (hr : 1 ≤ r) (a b : A) :
    Dab (r + 1) a b = b ^ (r - 1) - a * Dab r a b := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  unfold Dab
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [show n + 1 + 1 - 2 = n by omega, add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  rw [show n - (u + 1) = n - 1 - u by omega, show n + 1 - 2 - u = n - 1 - u by omega]
  ring

/-- Auxiliary for **(A2)** of `q_oddbox_shapes.md`: for even `n` and `u ≤ n`,
`(−1)^{n−u} = (−1)^u`. -/
lemma neg_one_pow_sub_of_even {n u : ℕ} (hn : Even n) (hu : u ≤ n) :
    ((-1 : A) ^ (n - u)) = (-1) ^ u := by
  have h : ((-1 : A) ^ (n - u)) * (-1) ^ u = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hu, hn.neg_one_pow]
  calc ((-1 : A) ^ (n - u)) = (-1) ^ (n - u) * ((-1) ^ u * (-1) ^ u) := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
    _ = (-1) ^ u := by rw [← mul_assoc, h, one_mul]

/-- **(A2)** of `q_oddbox_shapes.md`, first identity (`r` odd): `D(b, a) = D(a, b)`, i.e.
`Dab (r+1) b a = Dab (r+1) a b`. -/
theorem A2_D (r : ℕ) (hr : Odd r) (a b : A) : Dab (r + 1) b a = Dab (r + 1) a b := by
  unfold Dab
  rw [Nat.add_sub_cancel, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  have he : Even (r - 1) := by obtain ⟨k, rfl⟩ := hr; simp
  rw [neg_one_pow_sub_of_even he (by omega), show r + 1 - 2 - (r - 1 - u) = u by omega,
    show r + 1 - 2 - u = r - 1 - u by omega]
  ring

/-- **(A2)** of `q_oddbox_shapes.md`, second identity (`r` odd): `D^−(b, a) = −D^−(a, b)`, i.e.
`Dab r b a = −Dab r a b`. -/
theorem A2_Dminus (r : ℕ) (hr : Odd r) (a b : A) : Dab r b a = -Dab r a b := by
  unfold Dab
  rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  obtain ⟨k, rfl⟩ := hr
  have he : Even (2 * k) := even_two_mul k
  have h1 : (-1 : A) ^ (2 * k + 1 - 1 - 1 - u) = -(-1) ^ u := by
    have h2 := neg_one_pow_sub_of_even (A := A) he (show u + 1 ≤ 2 * k by omega)
    rw [show 2 * k + 1 - 1 - 1 - u = 2 * k - (u + 1) by omega, h2, pow_succ]
    ring
  rw [h1, show 2 * k + 1 - 2 - (2 * k + 1 - 1 - 1 - u) = u by omega,
    show 2 * k + 1 - 1 - 1 - u = 2 * k + 1 - 2 - u by omega]
  ring

/-- **(A3)** of `q_oddbox_shapes.md`, first identity (`r` odd): `(a + b)·D(a, b) = a^r + b^r`. -/
theorem A3_D (r : ℕ) (hr : Odd r) (a b : A) : (a + b) * Dab (r + 1) a b = a ^ r + b ^ r := by
  rw [A0, Nat.add_sub_cancel, hr.neg_pow]
  ring

/-- **(A3)** of `q_oddbox_shapes.md`, second identity (`r` odd):
`(a + b)·D^−(a, b) = b^{r−1} − a^{r−1}`. -/
theorem A3_Dminus (r : ℕ) (hr : Odd r) (a b : A) :
    (a + b) * Dab r a b = b ^ (r - 1) - a ^ (r - 1) := by
  have he : Even (r - 1) := by obtain ⟨k, rfl⟩ := hr; simp
  rw [A0, he.neg_pow]

/-- **(A4)** of `q_oddbox_shapes.md`, first displayed formula (`r` odd):
`D(a, b) = Σ_{u=0}^{r−1} (−1)^u b^u a^{r−1−u}`. -/
theorem A4_D (r : ℕ) (hr : Odd r) (a b : A) :
    Dab (r + 1) a b = ∑ u ∈ Finset.range r, (-1) ^ u * b ^ u * a ^ (r - 1 - u) := by
  rw [← A2_D r hr a b]
  unfold Dab
  rw [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show r + 1 - 2 - u = r - 1 - u by omega]

/-- **(A4)** of `q_oddbox_shapes.md`, second displayed formula (`r` odd):
`D^−(a, b) = −Σ_{u=0}^{r−2} (−1)^u b^u a^{r−2−u}`. -/
theorem A4_Dminus (r : ℕ) (hr : Odd r) (a b : A) :
    Dab r a b = -∑ u ∈ Finset.range (r - 1), (-1) ^ u * b ^ u * a ^ (r - 2 - u) := by
  rw [← neg_eq_iff_eq_neg, ← A2_Dminus r hr a b]
  rfl

open Polynomial in
/-- **(A4)** of `q_oddbox_shapes.md`, coefficient form for `D` (`r` odd): in `A[X]`, with `b ∈ A`
seen as the constant `C b`, the polynomial `Dab (r+1) X (C b)` has, for `0 ≤ u ≤ r − 1`, the
coefficient `(−1)^u b^u` at `X^{r−1−u}`. -/
theorem A4_coeff_D (r : ℕ) (hr : Odd r) (b : A) (u : ℕ) (hu : u ≤ r - 1) :
    (Dab (r + 1) (X : A[X]) (C b)).coeff (r - 1 - u) = (-1) ^ u * b ^ u := by
  have hr1 : 1 ≤ r := hr.pos
  rw [A4_D r hr, finset_sum_coeff]
  have : ∀ v ∈ Finset.range r, ((-1 : A[X]) ^ v * C b ^ v * X ^ (r - 1 - v)).coeff (r - 1 - u) =
      if v = u then (-1) ^ u * b ^ u else 0 := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [show ((-1 : A[X]) ^ v * C b ^ v) = C ((-1) ^ v * b ^ v) by simp, coeff_C_mul_X_pow]
    by_cases hvu : v = u
    · subst hvu; simp
    · rw [if_neg (by omega), if_neg hvu]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (by omega))]

open Polynomial in
/-- **(A4)** of `q_oddbox_shapes.md`, coefficient form for `D^−` (`r` odd): in `A[X]`, with
`b ∈ A` seen as the constant `C b`, the polynomial `Dab r X (C b)` has, for `0 ≤ u ≤ r − 2`
(written `u + 2 ≤ r`, so that the range is empty for `r = 1`, as in the file), the coefficient
`−(−1)^u b^u` at `X^{r−2−u}`. -/
theorem A4_coeff_Dminus (r : ℕ) (hr : Odd r) (b : A) (u : ℕ) (hu : u + 2 ≤ r) :
    (Dab r (X : A[X]) (C b)).coeff (r - 2 - u) = -((-1) ^ u * b ^ u) := by
  rw [A4_Dminus r hr, coeff_neg, finset_sum_coeff]
  congr 1
  have : ∀ v ∈ Finset.range (r - 1),
      ((-1 : A[X]) ^ v * C b ^ v * X ^ (r - 2 - v)).coeff (r - 2 - u) =
      if v = u then (-1) ^ u * b ^ u else 0 := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [show ((-1 : A[X]) ^ v * C b ^ v) = C ((-1) ^ v * b ^ v) by simp, coeff_C_mul_X_pow]
    by_cases hvu : v = u
    · subst hvu; simp
    · rw [if_neg (by omega), if_neg hvu]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (by omega))]

end OddShapes
