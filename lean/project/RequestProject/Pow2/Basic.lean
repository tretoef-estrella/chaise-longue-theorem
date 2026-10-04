module

public import RequestProject.ColSurv.Defs
public import RequestProject.ColOne.Sum

/-!
# Degree `2^v`: the two identities in characteristic `2` (`q_pow2_leading.md`, (i) and (v)(a))

This file formalizes parts **(i)** and **(v)(a)** of the **Theorem** of `q_pow2_leading.md`.
Both are proved as in the **Proof** of the file: by cancelling `u + 1` (resp. `a + b`) in a
polynomial ring over `ZMod 2` (a domain) and mapping to the given ring.

The proofs only use `(2 : A) = 0`; the statements with `[CharP A 2]` are deduced from the
versions `phi_two_pow_of_two_eq_zero` and `mul_add_pow_of_two_eq_zero`.
-/

@[expose] public section

open Polynomial

namespace Pow2

/-- **Proof of (i)** of `q_pow2_leading.md`: a ring homomorphism `ZMod 2 → A` for every ring `A`
with `2 = 0`. -/
noncomputable def zmod2Hom (A : Type*) [CommRing A] (h2 : (2 : A) = 0) : ZMod 2 →+* A where
  toFun x := if x = 0 then 0 else 1
  map_one' := by simp
  map_mul' x y := by fin_cases x <;> fin_cases y <;> simp
  map_zero' := by simp
  map_add' x y := by
    fin_cases x <;> fin_cases y <;> simp
    · rw [if_pos (by decide), one_add_one_eq_two, h2]

/-- **Proof of (i)** of `q_pow2_leading.md`: `φ_m` commutes with ring homomorphisms. -/
theorem map_phi {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') (m : ℕ) (u : A) :
    f (ColSurv.phi m u) = ColSurv.phi m (f u) := by
  simp [ColSurv.phi, map_sum, map_pow]

/-- **Proof of (i)** of `q_pow2_leading.md`: in `F_2[u]`, `φ_q(u) = (u + 1)^{q−1}` for `q = 2^v`
(obtained by cancelling `u + 1` from `(u + 1)·φ_q(u) = u^q + 1 = (u + 1)^q`). -/
theorem phi_two_pow_zmod (v : ℕ) :
    ColSurv.phi (2 ^ v) (X : (ZMod 2)[X]) = (X + 1) ^ (2 ^ v - 1) := by
  have hne : (X + 1 : (ZMod 2)[X]) ≠ 0 := X_add_C_ne_zero 1
  apply mul_left_cancel₀ hne
  have h1 : (X + 1 : (ZMod 2)[X]) * ColSurv.phi (2 ^ v) X = X ^ (2 ^ v) - 1 := by
    rw [ColSurv.phi, mul_comm, ← geom_sum_mul]
    congr 1
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [h1, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_two_pow), add_pow_char_pow, one_pow,
    sub_eq_add_neg, CharTwo.neg_eq]

/-- **(i)** of `q_pow2_leading.md`, in the slightly more general form where only `2 = 0` in `A` is
assumed: `φ_q(u) = (u + 1)^{q−1}` for `q = 2^v`. -/
theorem phi_two_pow_of_two_eq_zero {A : Type*} [CommRing A] (h2 : (2 : A) = 0) (u : A) (v : ℕ) :
    ColSurv.phi (2 ^ v) u = (u + 1) ^ (2 ^ v - 1) := by
  have := congrArg (Polynomial.eval₂RingHom (zmod2Hom A h2) u) (phi_two_pow_zmod v)
  rw [map_phi, map_pow, map_add, map_one] at this
  simpa using this

/-- **(i) (`φ` in characteristic `2`)** of `q_pow2_leading.md`: for every commutative ring `A` of
characteristic `2`, every `u ∈ A` and `q = 2^v` (`v ≥ 0`): `φ_q(u) = (u + 1)^{q−1}`. -/
theorem phi_two_pow {A : Type*} [CommRing A] [CharP A 2] (u : A) (v : ℕ) :
    ColSurv.phi (2 ^ v) u = (u + 1) ^ (2 ^ v - 1) :=
  phi_two_pow_of_two_eq_zero (CharTwo.two_eq_zero) u v

/-- **Proof of (v)(a)** of `q_pow2_leading.md`: in `F_2[a, b]`,
`(a + b)^{q−1} = Σ_{u=0}^{q−1} a^u b^{q−1−u}` for `q = 2^v` (obtained by cancelling `a + b` from
`(a + b)·Σ_{u=0}^{q−1} a^u b^{q−1−u} = a^q + b^q = (a + b)^q`). -/
theorem add_pow_two_pow_sub_one_zmod (v : ℕ) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 2)) ^ (2 ^ v - 1) =
      ∑ u ∈ Finset.range (2 ^ v),
        MvPolynomial.X 0 ^ u * MvPolynomial.X 1 ^ (2 ^ v - 1 - u) := by
  set a : MvPolynomial (Fin 2) (ZMod 2) := MvPolynomial.X 0
  set b : MvPolynomial (Fin 2) (ZMod 2) := MvPolynomial.X 1
  have hne : a + b ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![1, 0]) h
    simp [a, b] at this
  apply mul_left_cancel₀ hne
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_two_pow), add_pow_char_pow, mul_comm,
    show a + b = a - b by rw [sub_eq_add_neg, CharTwo.neg_eq], geom_sum₂_mul, sub_eq_add_neg,
    CharTwo.neg_eq]

/-- **(v)(a)** of `q_pow2_leading.md`, in the slightly more general form where only `2 = 0` in `A`
is assumed: for `q = 2^v` with `v ≥ 1` and `a, b ∈ A` with `b^q = 0`,
`b·(a + b)^{q−1} = a·b·D(a, b)`. -/
theorem mul_add_pow_of_two_eq_zero {A : Type*} [CommRing A] (h2 : (2 : A) = 0) {v : ℕ}
    (hv : 1 ≤ v) (a b : A) (hb : b ^ (2 ^ v) = 0) :
    b * (a + b) ^ (2 ^ v - 1) = a * b * ColOne.Dab (2 ^ v) a b := by
  have key := congrArg (MvPolynomial.eval₂Hom (zmod2Hom A h2) ![a, b])
    (add_pow_two_pow_sub_one_zmod v)
  simp only [map_pow, map_add, map_sum, map_mul, MvPolynomial.eval₂Hom_X'] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at key
  have hneg : (-1 : A) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have hq2 : 2 ≤ 2 ^ v := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ v = r + 2 := ⟨2 ^ v - 2, by omega⟩
  rw [key, hr]
  rw [hr] at hb
  rw [ColOne.Dab, Finset.mul_sum, Finset.mul_sum, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, show r + 2 - 1 - 0 = r + 1 by omega]
  rw [← pow_succ', hb, add_zero, show r + 2 - 1 = r + 1 by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  rw [show r + 1 - (u + 1) = r - u by omega, show r + 2 - 2 - u = r - u by omega, hneg, one_pow]
  ring

/-- **(v)(a) (the leading forms)** of `q_pow2_leading.md`: for every commutative ring `A` of
characteristic `2`, `q = 2^v` with `v ≥ 1`, and `a, b ∈ A` with `b^q = 0`:
`b·(a + b)^{q−1} = a·b·D(a, b)`. -/
theorem mul_add_pow {A : Type*} [CommRing A] [CharP A 2] {v : ℕ} (hv : 1 ≤ v) (a b : A)
    (hb : b ^ (2 ^ v) = 0) :
    b * (a + b) ^ (2 ^ v - 1) = a * b * ColOne.Dab (2 ^ v) a b :=
  mul_add_pow_of_two_eq_zero CharTwo.two_eq_zero hv a b hb

end Pow2

end
