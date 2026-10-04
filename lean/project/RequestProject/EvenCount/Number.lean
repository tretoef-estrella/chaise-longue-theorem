module

public import RequestProject.EvenCount.Defs

/-!
# Parts (i) and (vii) of the Theorem of `q_even_count.md`: the number `Q^e_k(m)`

* `QkEven_eq` (Theorem (i)): `Q^e_k(m) = 1 + Σ_{c=0}^{k} C(2k+2, 2c) · Q_{k−c}(m − 1)`;
* `QkEven_values` (Theorem (vii)): `Q^e_1(4) = 19`, `Q^e_2(4) = 141`, `Q^e_1(6) = 61`.
-/

@[expose] public section

namespace EvenCount

open TheoremB

/-- **Proof of (i)** in `q_even_count.md` (auxiliary): `b_u ≤ b_1 + ⋯ + b_h`. -/
theorem le_sum_fin {h : ℕ} (b : Fin h → ℕ) (u : Fin h) : b u ≤ ∑ v, b v :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)

/-- **Proof of (i)** in `q_even_count.md` (auxiliary, "each term is an integer"):
`Π_u (b_u!)^2` divides `(2(b_1 + ⋯ + b_h))!` (a multinomial coefficient). -/
theorem prod_sq_factorial_dvd {h : ℕ} (b : Fin h → ℕ) :
    ∏ u, (b u).factorial ^ 2 ∣ (2 * ∑ u, b u).factorial := by
  have h1 : ∏ u, (b u).factorial ^ 2 = ∏ t : Fin h × Bool, (b t.1).factorial := by
    rw [Fintype.prod_prod_type]
    simp only [Fintype.prod_bool]
    exact Finset.prod_congr rfl fun u _ => by ring
  have h2 : 2 * ∑ u, b u = ∑ t : Fin h × Bool, b t.1 := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [h1, h2]
  exact Nat.prod_factorial_dvd_factorial_sum _ _

/-- **Proof of (i)** in `q_even_count.md`: for `c ≤ k` and `2 Σ b_u = N − 2c`,
`N!/((2c)! Π (b_u!)^2) = C(N, 2c) · (N − 2c)!/Π (b_u!)^2`, with `N = 2k + 2`. -/
theorem term_eq {h k c : ℕ} (hc : c ≤ k) (b : Fin h → ℕ)
    (hb : 2 * ∑ u, b u = 2 * (k - c) + 2) :
    (2 * k + 2).factorial / ((2 * c).factorial * ∏ u, (b u).factorial ^ 2) =
      (2 * k + 2).choose (2 * c) *
        ((2 * (k - c) + 2).factorial / ∏ u, (b u).factorial ^ 2) := by
  obtain ⟨q, hq⟩ := prod_sq_factorial_dvd b
  rw [hb] at hq
  have hP : 0 < ∏ u, (b u).factorial ^ 2 :=
    Finset.prod_pos fun u _ => pow_pos (Nat.factorial_pos _) 2
  have hsub : 2 * k + 2 - 2 * c = 2 * (k - c) + 2 := by omega
  have hch := Nat.choose_mul_factorial_mul_factorial (n := 2 * k + 2) (k := 2 * c) (by omega)
  rw [hsub, hq] at hch
  rw [hq, Nat.mul_div_cancel_left _ hP]
  apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (Nat.factorial_pos _) hP)
  rw [← hch]
  ring

/-- **Theorem (i)** of `q_even_count.md` (the number, by the multiplicity of the fixed point):
`Q^e_k(m) = 1 + Σ_{c=0}^{k} C(2k+2, 2c) · Q_{k−c}(m − 1)`.
The file assumes `m` even and `m ≥ 2`; the identity holds for every `m` (both sides only depend
on `h = (m − 2)/2 = ((m − 1) − 1)/2`), so these hypotheses are dropped and the statement is more
general. -/
theorem QkEven_eq (k m : ℕ) :
    QkEven k m =
      1 + ∑ c ∈ Finset.range (k + 1), (2 * k + 2).choose (2 * c) * Qk (k - c) (m - 1) := by
  unfold QkEven
  rw [Finset.sum_range_succ, add_comm]
  congr 1
  · -- the term `c = k + 1`
    have hfil : (Fintype.piFinset fun _ : Fin ((m - 2) / 2) => Finset.range (2 * k + 3)).filter
        (fun b => 2 * (k + 1) + 2 * ∑ u, b u = 2 * k + 2) = {0} := by
      ext b
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hb⟩
        funext u
        have := le_sum_fin b u
        simp only [Pi.zero_apply]
        omega
      · rintro rfl
        simp
        ring
    rw [hfil, Finset.sum_singleton]
    simp only [Pi.zero_apply, Nat.factorial_zero, one_pow, Finset.prod_const_one, mul_one]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, Nat.div_self (Nat.factorial_pos _)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    have hc' : c ≤ k := by omega
    unfold Qk
    rw [show (m - 1 - 1) / 2 = (m - 2) / 2 by omega, Finset.mul_sum]
    have hfil : (Fintype.piFinset fun _ : Fin ((m - 2) / 2) => Finset.range (2 * k + 3)).filter
          (fun b => 2 * c + 2 * ∑ u, b u = 2 * k + 2) =
        (Fintype.piFinset fun _ : Fin ((m - 2) / 2) => Finset.range (2 * (k - c) + 3)).filter
          (fun b => 2 * ∑ u, b u = 2 * (k - c) + 2) := by
      ext b
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · rintro ⟨-, hb⟩
        refine ⟨fun u => ?_, by omega⟩
        have := le_sum_fin b u
        omega
      · rintro ⟨-, hb⟩
        refine ⟨fun u => ?_, by omega⟩
        have := le_sum_fin b u
        omega
    rw [hfil]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    exact term_eq hc' b hb.2

/-- **Theorem (vii)** of `q_even_count.md` (first values): `Q^e_1(4) = 19`, `Q^e_2(4) = 141`,
`Q^e_1(6) = 61`, evaluated from the definition by a kernel-checked computation. -/
theorem QkEven_values : QkEven 1 4 = 19 ∧ QkEven 2 4 = 141 ∧ QkEven 1 6 = 61 := by
  decide

end EvenCount

end
