module

public import RequestProject.ColSurv.Defs

/-!
# Lemma 6.2 of `q_col_survivors.md`: which generators survive on each factor

Parts **(i)**, **(ii)** and **(iii)** of **Lemma 6.2** of `q_col_survivors.md`, following the
**Proof** given there.  The Setting and the elementary facts are in
`RequestProject/ColSurv/Defs.lean`.
-/

@[expose] public section

open MvPolynomial

namespace ColSurv

open ColSplit

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

/-- The value of `t_a ∈ R_c` under `t ↦ c` is `c_a` (`1 ≤ a ≤ d`); see the *Units* paragraph of
the **Proof** of Lemma 6.2 in `q_col_survivors.md`. -/
theorem evalRc_tR (c : Fin (2 * k + 1) → S.μ) {a : Fin (2 * k + 2)} (ha : 0 < a) :
    evalRc S c (tR c a) = cExt c a := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.pos_iff_ne_zero.1 ha)
  simp [tR, cExt]

/-- *Frobenius in `R_c`* (**Proof** of Lemma 6.2 in `q_col_survivors.md`), for the indices
`1 ≤ a ≤ d`: `t_a^q = c_a^q`. -/
theorem frobenius_tR (c : Fin (2 * k + 1) → S.μ) {a : Fin (2 * k + 2)} (ha : 0 < a) :
    tR c a ^ S.q = algebraMap F _ (cExt c a ^ S.q) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.pos_iff_ne_zero.1 ha)
  exact frobenius_t S c j

/-- **Setting** of `q_col_survivors.md`: `(t_a − c_a)^q = 0` in `R_c` for `1 ≤ a ≤ d`. -/
theorem sub_pow_q_tR (c : Fin (2 * k + 1) → S.μ) {a : Fin (2 * k + 2)} (ha : 0 < a) :
    (tR c a - algebraMap F _ (cExt c a)) ^ S.q = 0 := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (Fin.pos_iff_ne_zero.1 ha)
  exact sub_pow_q_eq_zero S c j

/-- **Lemma 6.2 (i)** of `q_col_survivors.md`. Fix `c ∈ μ^d`. For `1 ≤ i ≤ d`: if `c_i ≠ 1`, then
`t_i − 1` is a unit of `R_c`; if `c_i = 1`, then `(t_i − 1)^q = 0` in `R_c`. -/
theorem lemma62_i (c : Fin (2 * k + 1) → S.μ) (i : Fin (2 * k + 2)) (hi : 0 < i) :
    (cExt c i ≠ 1 → IsUnit (tR c i - 1)) ∧ (cExt c i = 1 → (tR c i - 1) ^ S.q = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [isUnit_iff_evalRc_ne_zero, map_sub, map_one, evalRc_tR S c hi]
    exact sub_ne_zero.2 h
  · have := sub_pow_q_tR S c hi
    rwa [h, map_one] at this

/-- The polynomial identity of the **Proof** of Lemma 6.2 (ii) in `q_col_survivors.md`:
`φ(X) = (X − 1)^{q−1} · Π_{ξ ∈ μ, ξ ≠ 1} (X − ξ)^q` in `F[X]`, obtained from
`(X − 1)·φ(X) = X^m − 1 = Π_{ξ∈μ} (X − ξ)^q` (Lemma 6.1(0)) by cancelling `X − 1`. -/
theorem phi_X_eq [DecidableEq F] :
    phi S.m (Polynomial.X : Polynomial F) =
      (Polynomial.X - 1) ^ (S.q - 1) *
        ∏ ξ ∈ S.μ.erase 1, (Polynomial.X - Polynomial.C ξ) ^ S.q := by
  have h1 := Setting.one_mem_μ S
  have hq := Setting.one_le_q S
  refine mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : F)) ?_
  rw [map_one, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hq,
    ← map_one Polynomial.C, Finset.mul_prod_erase _ (fun ξ => (Polynomial.X - Polynomial.C ξ) ^ S.q)
      h1, ← ColSetting.lemma61_0_poly, map_one, phi, mul_comm, geom_sum_mul]

/-- **Lemma 6.2 (ii)** of `q_col_survivors.md`. Fix `c ∈ μ^d`, let `1 ≤ j < l ≤ d` and
`u := t_j t_l ∈ R_c`. If `c_j c_l ≠ 1`, then `φ(u) = 0` in `R_c`. If `c_j c_l = 1`, then
`φ(u) = w·(u − 1)^{q−1}` for a unit `w` of `R_c`. -/
theorem lemma62_ii (c : Fin (2 * k + 1) → S.μ) (j l : Fin (2 * k + 2)) (hj : 0 < j)
    (hjl : j < l) :
    (cExt c j * cExt c l ≠ 1 → phi S.m (tR c j * tR c l) = 0) ∧
      (cExt c j * cExt c l = 1 →
        ∃ w : (Rc F S.q (fun i => (c i : F)))ˣ,
          phi S.m (tR c j * tR c l) = w * (tR c j * tR c l - 1) ^ (S.q - 1)) := by
  classical
  have hl : 0 < l := hj.trans hjl
  set u := tR c j * tR c l with hu
  set ξ0 := cExt c j * cExt c l with hξ0
  have hξ0μ : ξ0 ∈ S.μ := Setting.mul_mem_μ S (cExt_mem c j) (cExt_mem c l)
  have hev : evalRc S c u = ξ0 := by
    rw [hu, map_mul, evalRc_tR S c hj, evalRc_tR S c hl]
  have hnil : (u - algebraMap F _ ξ0) ^ S.q = 0 := by
    rw [frobenius_sub, hu, mul_pow, frobenius_tR S c hj, frobenius_tR S c hl, ← map_mul,
      ← mul_pow, ← hξ0, ← map_pow, sub_self]
  have hphi : phi S.m u = (u - 1) ^ (S.q - 1) *
      ∏ ξ ∈ S.μ.erase 1, (u - algebraMap F _ ξ) ^ S.q := by
    have := congrArg (Polynomial.aeval u) (phi_X_eq S)
    simpa [map_phi, map_prod] using this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hphi, Finset.prod_eq_zero (f := fun ξ => (u - algebraMap F _ ξ) ^ S.q)
      (Finset.mem_erase.2 ⟨h, hξ0μ⟩) hnil, mul_zero]
  · have hw : IsUnit (∏ ξ ∈ S.μ.erase 1, (u - algebraMap F _ ξ) ^ S.q) := by
      refine (IsUnit.prod_iff).2 fun ξ hξ => IsUnit.pow _ ?_
      rw [isUnit_iff_evalRc_ne_zero, map_sub, hev, AlgHom.commutes, h]
      exact sub_ne_zero.2 (Ne.symm (Finset.mem_erase.1 hξ).1)
    exact ⟨hw.unit, by rw [hphi, IsUnit.unit_spec]; exact mul_comm _ _⟩

/-- For a matching `J` (a fixed-point-free involution of `{0, …, d}`), the pairs `{a, J(a)}`
partition `{0, …, d}`: `Π_a f(a) = Π_{a < J(a)} f(a) f(J(a))` (**Proof** of Lemma 6.2 (iii) in
`q_col_survivors.md`). -/
theorem prod_eq_prod_pairs {M : Type*} [CommMonoid M] (J : BallotBound.Matching k)
    (f : Fin (2 * k + 2) → M) :
    ∏ a, f a = ∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), f a * f (J.1 a) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun a => a < J.1 a)]
  congr 1
  refine Finset.prod_nbij' J.1 J.1 ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha ⊢
    rw [(J.2 a).2]
    exact lt_of_le_of_ne ha (J.2 a).1
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha ⊢
    rw [(J.2 a).2]
    exact ha.le
  · intro a _; exact (J.2 a).2
  · intro a _; exact (J.2 a).2
  · intro a _; rw [(J.2 a).2]

/-- Collecting units: if `f(i) = w_i · g(i)` with units `w_i`, then `Π f = w · Π g` with the unit
`w = Π w_i` (last step of the **Proof** of Lemma 6.2 (iii) in `q_col_survivors.md`). -/
theorem exists_unit_prod {M ι : Type*} [CommMonoid M] (s : Finset ι) (f g : ι → M)
    (h : ∀ i ∈ s, ∃ w : Mˣ, f i = w * g i) : ∃ w : Mˣ, ∏ i ∈ s, f i = w * ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨wa, hwa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨wa * w, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hw, hwa, Units.val_mul,
      mul_mul_mul_comm]

/-- `π_c(ψ_J) = Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} φ(t_a t_{J(a)})` computed in `R_c`
(**Setting** of `q_col_survivors.md`: `t_a` also denotes the image of the variable in `R_c`). -/
theorem piC_psi (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k) :
    S.piC c (psi S k J) =
      (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tR c (J.1 a) - 1)) *
        ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), phi S.m (tR c a * tR c (J.1 a)) := by
  simp [psi, map_prod, map_phi, piC_tG]

/-- **Lemma 6.2 (iii)** of `q_col_survivors.md`. Fix `c ∈ μ^d` and a matching `J`. If some pair
`{a, J(a)}` with `0 < a < J(a)` has `c_a c_{J(a)} ≠ 1`, then `π_c(ψ_J) = 0`. If
`c_a c_{J(a)} = 1` for every pair with `0 < a < J(a)`, then also `c_0 c_{J(0)} = 1`, and
`π_c(ψ_J) = w · Π_{a < J(a)} (t_{J(a)} − 1) · Π_{0 < a < J(a)} (t_a t_{J(a)} − 1)^{q−1}` (6.2)
for a unit `w` of `R_c`. -/
theorem lemma62_iii (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k) :
    ((∃ a, 0 < a ∧ a < J.1 a ∧ cExt c a * cExt c (J.1 a) ≠ 1) → S.piC c (psi S k J) = 0) ∧
      ((∀ a, 0 < a → a < J.1 a → cExt c a * cExt c (J.1 a) = 1) →
        cExt c 0 * cExt c (J.1 0) = 1 ∧
          ∃ w : (Rc F S.q (fun i => (c i : F)))ˣ,
            S.piC c (psi S k J) =
              w * (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tR c (J.1 a) - 1)) *
                ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a),
                  (tR c a * tR c (J.1 a) - 1) ^ (S.q - 1)) := by
  refine ⟨fun ⟨a, ha, haJ, hc⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
  · rw [piC_psi]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := a) (by simp [ha, haJ])
      ((lemma62_ii S c a (J.1 a) ha haJ).1 hc))
  · have h0 : (0 : Fin (2 * k + 2)) ∈ Finset.univ.filter (fun a => a < J.1 a) := by
      simpa [Fin.pos_iff_ne_zero] using (J.2 0).1
    have := (prod_eq_prod_pairs J (cExt c)).symm
    rw [prod_cExt, ← Finset.mul_prod_erase _ _ h0, Finset.prod_eq_one, mul_one] at this
    · exact this
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact h a (Fin.pos_iff_ne_zero.2 ha.1) ha.2
  · obtain ⟨w, hw⟩ := exists_unit_prod (Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a))
      (fun a => phi S.m (tR c a * tR c (J.1 a)))
      (fun a => (tR c a * tR c (J.1 a) - 1) ^ (S.q - 1)) (fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact (lemma62_ii S c a (J.1 a) ha.1 ha.2).2 (h a ha.1 ha.2))
    refine ⟨w, ?_⟩
    rw [piC_psi, hw]
    ring

end ColSurv

end
