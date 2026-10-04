module

public import RequestProject.Pow2.Basic
public import RequestProject.ColUpper.Defs
public import RequestProject.TheoremB.Defs

/-!
# Degree `2^v`: the ring, the generators and the leading forms
(`q_pow2_leading.md`, (ii), (iii), (v)(b))

This file formalizes the **Setting** of `q_pow2_leading.md` (the polynomials `P_J`, `L_J`, `E_J`)
and parts **(ii)**, **(iii)** and **(v)(b)** of its **Theorem**.

Conventions (as in the existing files):
* `F[G] = F[t_1, …, t_d]/(t_i^q − 1)` is `ColSplit.GA F d q`;
* `B = F[s_1, …, s_d]/(s_i^q)` is `Peel.C F (q + 1) d` and `C = F[y_1, …, y_d]/(y_i^{q−1})` is
  `Peel.C F q d`; in both, the variable of index `i : Fin d` is the class of `X i`;
* the vertex `a ∈ {1, …, 2k+1}` of a matching (`a : Fin (2 * k + 2)`, `a ≠ 0`) carries the
  variable `X (TheoremB.idx a)` (the index `a − 1`);
* a pair `{a < J(a)}` of a matching `J` is recorded by its smaller element `a`.
-/

@[expose] public section

open MvPolynomial

namespace Pow2

set_option synthInstance.maxHeartbeats 200000

/-! ### The polynomials `P_J`, `L_J`, `E_J` -/

section Polys

variable (F : Type*) [Field F] (q : ℕ)

/-- **Setting** of `q_pow2_leading.md`: for a matching `J`, the polynomial
`P_J := Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} (s_a + s_{J(a)} + s_a s_{J(a)})^{q−1}` of
`F[s_1, …, s_{2k+1}]` (the vertex `a` carries the variable `X (idx a)`). -/
noncomputable def PJ {k : ℕ} (J : BallotBound.Matching k) : MvPolynomial (Fin (2 * k + 1)) F :=
  (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), X (TheoremB.idx (J.1 a))) *
    ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a),
      (X (TheoremB.idx a) + X (TheoremB.idx (J.1 a)) +
        X (TheoremB.idx a) * X (TheoremB.idx (J.1 a))) ^ (q - 1)

/-- **Setting** of `q_pow2_leading.md`: for a matching `J`, the polynomial
`L_J := Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} (s_a + s_{J(a)})^{q−1}` of
`F[s_1, …, s_{2k+1}]`. -/
noncomputable def LJ {k : ℕ} (J : BallotBound.Matching k) : MvPolynomial (Fin (2 * k + 1)) F :=
  (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), X (TheoremB.idx (J.1 a))) *
    ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a),
      (X (TheoremB.idx a) + X (TheoremB.idx (J.1 a))) ^ (q - 1)

/-- **Setting** of `q_pow2_leading.md`: for a matching `J`, the polynomial
`E_J := Π_{0 < a < J(a)} D(s_a, s_{J(a)})` of `F[s_1, …, s_{2k+1}]`, with
`D(a, b) = Σ_{w=0}^{q−2} (−1)^w a^w b^{q−2−w}` (`ColOne.Dab`). -/
noncomputable def EJ {k : ℕ} (J : BallotBound.Matching k) : MvPolynomial (Fin (2 * k + 1)) F :=
  ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a),
    ColOne.Dab q (X (TheoremB.idx a)) (X (TheoremB.idx (J.1 a)))

/-- **Setting** of `q_pow2_leading.md`: the pairs `{a < J(a)}` avoiding `0` are the `a` with
`0 < a < J(a)` (the filter used in `TheoremB.DJ`). -/
theorem filter_avoid_zero {k : ℕ} (J : BallotBound.Matching k) :
    Finset.univ.filter (fun a => a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a) =
      Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨Fin.pos_iff_ne_zero.2 h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨Fin.pos_iff_ne_zero.1 h1, (lt_of_le_of_lt (Fin.zero_le a) h3).ne', h3⟩

/-- **Setting** of `q_pow2_leading.md`: the class of `E_J` in `C` (reading `s` as `y`) is `D_J`
(`TheoremB.DJ`). -/
theorem mk_EJ {k : ℕ} (J : BallotBound.Matching k) :
    Ideal.Quotient.mk (Peel.powIdeal F q (2 * k + 1)) (EJ F q J) = TheoremB.DJ F q J := by
  rw [TheoremB.DJ, filter_avoid_zero, EJ, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [ColOne.map_Dab, ColOne.D_eq_Dab]
  rfl

end Polys

/-! ### (ii) The isomorphism `Θ` -/

section Theta

variable (F : Type*) [Field F] [CharP F 2]

/-- **Proof of (ii)** of `q_pow2_leading.md`: the `F`-algebra endomorphism `τ` of
`F[x_1, …, x_d]` with `τ(x_i) = x_i + 1`. -/
noncomputable def tauHom (d : ℕ) : MvPolynomial (Fin d) F →ₐ[F] MvPolynomial (Fin d) F :=
  aeval fun i => X i + 1

/-- **Proof of (ii)** of `q_pow2_leading.md`: `τ ∘ τ` is the identity (characteristic `2`). -/
theorem tauHom_comp_tauHom (d : ℕ) : (tauHom F d).comp (tauHom F d) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro i
  have h2 : (2 : MvPolynomial (Fin d) F) = 0 := CharTwo.two_eq_zero
  simp only [tauHom, AlgHom.comp_apply, aeval_X, map_add, map_one, AlgHom.id_apply]
  linear_combination h2

/-- **Proof of (ii)** of `q_pow2_leading.md`: `τ` as an automorphism of `F[x_1, …, x_d]`. -/
noncomputable def tauEquiv (d : ℕ) : MvPolynomial (Fin d) F ≃ₐ[F] MvPolynomial (Fin d) F :=
  AlgEquiv.ofAlgHom (tauHom F d) (tauHom F d) (tauHom_comp_tauHom F d) (tauHom_comp_tauHom F d)

/-- **Proof of (ii)** of `q_pow2_leading.md`: `τ` maps the ideal `(x_i^q − 1 : i)` onto the ideal
`(x_i^q : i)`, for `q = 2^v`. -/
theorem map_gaIdeal (d v : ℕ) :
    (ColSplit.gaIdeal F d (2 ^ v)).map (tauEquiv F d) = Peel.powIdeal F (2 ^ v + 1) d := by
  rw [ColSplit.gaIdeal, Ideal.map_span, Peel.powIdeal, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  rw [Function.comp_apply, Nat.add_sub_cancel]
  change tauHom F d (X i ^ 2 ^ v - 1) = X i ^ 2 ^ v
  rw [map_sub, map_pow, map_one, tauHom, aeval_X, add_pow_char_pow, one_pow, add_sub_cancel_right]

/-- **(ii) (the ring)** of `q_pow2_leading.md`: the isomorphism of `F`-algebras
`Θ : F[G] = F[t]/(t_i^q − 1) → B = F[s]/(s_i^q)` (`q = 2^v`, any number `d` of variables), induced
by `τ`. -/
noncomputable def Theta (d v : ℕ) : ColSplit.GA F d (2 ^ v) ≃ₐ[F] Peel.C F (2 ^ v + 1) d :=
  Ideal.quotientEquivAlg _ _ (tauEquiv F d) (map_gaIdeal F d v).symm

variable {F}

/-- **Proof of (ii)** of `q_pow2_leading.md`: `Θ` on classes of polynomials. -/
theorem Theta_mk (d v : ℕ) (p : MvPolynomial (Fin d) F) :
    Theta F d v (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (tauHom F d p) := rfl

/-- **(ii) (the ring)** of `q_pow2_leading.md`: `Θ(t_i) = 1 + s_i` for every `i`. -/
theorem Theta_X (d v : ℕ) (i : Fin d) :
    Theta F d v (Ideal.Quotient.mk _ (X i)) = 1 + Tight.y F (2 ^ v + 1) i := by
  rw [Theta_mk, tauHom, aeval_X, map_add, map_one]
  exact add_comm _ _

/-- **(ii) (the ring)** of `q_pow2_leading.md`, both claims together: there is an isomorphism of
`F`-algebras `Θ : F[G] → B` with `Θ(t_i) = 1 + s_i` for all `i` (for every `d`). -/
theorem exists_Theta (d v : ℕ) :
    ∃ Θ : ColSplit.GA F d (2 ^ v) ≃ₐ[F] Peel.C F (2 ^ v + 1) d,
      ∀ i : Fin d, Θ (Ideal.Quotient.mk _ (X i)) = 1 + Tight.y F (2 ^ v + 1) i :=
  ⟨Theta F d v, Theta_X d v⟩

end Theta

/-! ### (iii) The generators -/

section Generators

variable {F : Type*} [Field F]

/-- **Proof of (iii)** of `q_pow2_leading.md`: in `B` (and in every `Peel.C F (q + 1) d`),
`2 = 0`. -/
theorem two_eq_zero_C [CharP F 2] (q d : ℕ) : (2 : Peel.C F q d) = 0 := by
  have h : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [← map_ofNat (algebraMap F (Peel.C F q d)) 2, h, map_zero]

/-- **Setting** of `q_col_upper.md` / `q_pow2_leading.md`: for a vertex `a ≠ 0`, `t_a` is the class
of the variable `X (idx a)`. -/
theorem tU_of_ne_zero (m k : ℕ) {a : Fin (2 * k + 2)} (ha : a ≠ 0) :
    ColUpper.tU F m k a = Ideal.Quotient.mk _ (X (TheoremB.idx a)) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 ha
  have : TheoremB.idx j.succ = j := Fin.ext (by simp [TheoremB.idx])
  rw [this]
  rfl

/-- **(iii) (the generators)** of `q_pow2_leading.md`: for every matching `J`, `Θ(ψ_J)` is the
class of `P_J` in `B`. -/
theorem Theta_psiG [CharP F 2] (v : ℕ) {k : ℕ} (J : BallotBound.Matching k) :
    Theta F (2 * k + 1) v (ColUpper.psiG F (2 ^ v) J) =
      Ideal.Quotient.mk _ (PJ F (2 ^ v) J) := by
  have h2 := two_eq_zero_C (F := F) (2 ^ v + 1) (2 * k + 1)
  have hJ : ∀ a, a < J.1 a → J.1 a ≠ 0 := fun a h => (lt_of_le_of_lt (Fin.zero_le a) h).ne'
  rw [ColUpper.psiG, map_mul, map_prod, map_prod, PJ, map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [tU_of_ne_zero _ _ (hJ a ha.2), map_sub, map_one, Theta_X, add_sub_cancel_left]
    rfl
  · refine Finset.prod_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [tU_of_ne_zero _ _ (hJ a ha.2.2), tU_of_ne_zero _ _ (Fin.pos_iff_ne_zero.1 ha.2.1)]
    rw [show (Theta F (2 * k + 1) v : ColSplit.GA F (2 * k + 1) (2 ^ v) → _) =
      (Theta F (2 * k + 1) v : ColSplit.GA F (2 * k + 1) (2 ^ v) →+* _) from rfl, map_phi,
      RingHom.coe_coe, map_mul, Theta_X, Theta_X, phi_two_pow_of_two_eq_zero h2]
    simp only [map_pow, map_add, map_mul]
    congr 1
    change (1 + Tight.y F (2 ^ v + 1) (TheoremB.idx a)) *
        (1 + Tight.y F (2 ^ v + 1) (TheoremB.idx (J.1 a))) + 1 =
      Tight.y F (2 ^ v + 1) (TheoremB.idx a) + Tight.y F (2 ^ v + 1) (TheoremB.idx (J.1 a)) +
        Tight.y F (2 ^ v + 1) (TheoremB.idx a) * Tight.y F (2 ^ v + 1) (TheoremB.idx (J.1 a))
    linear_combination h2

end Generators

/-! ### (v)(b) The leading forms -/

section Leading

/-- **Proof of (v)(b)** of `q_pow2_leading.md`: the larger elements of the `k + 1` pairs of `J`
together with the smaller elements of the `k` pairs avoiding `0` are exactly `1, …, 2k+1`, each
once; hence `Π_{a < J(a)} s_{J(a)} · Π_{0 < a < J(a)} s_a = s_1 ⋯ s_d` (in any commutative
monoid). -/
theorem prod_pairs_eq {M : Type*} [CommMonoid M] {k : ℕ} (J : BallotBound.Matching k)
    (y : Fin (2 * k + 1) → M) :
    (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), y (TheoremB.idx (J.1 a))) *
        ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), y (TheoremB.idx a) =
      ∏ i, y i := by
  have hinv : ∀ a, J.1 (J.1 a) = a := fun a => (J.2 a).2
  have hne : ∀ a, J.1 a ≠ a := fun a => (J.2 a).1
  -- the first product, reindexed by `b = J(a)`
  have h1 : (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), y (TheoremB.idx (J.1 a))) =
      ∏ b ∈ Finset.univ.filter (fun b => J.1 b < b), y (TheoremB.idx b) := by
    refine Finset.prod_nbij' (fun a => J.1 a) (fun b => J.1 b) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [hinv]
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rwa [hinv]
    · intro a _; exact hinv a
    · intro b _; exact hinv b
    · intro a _; rfl
  -- the right-hand side, as a product over the vertices `b ≠ 0`
  have h2 : ∏ i, y i = ∏ b ∈ Finset.univ.filter (fun b : Fin (2 * k + 2) => b ≠ 0),
      y (TheoremB.idx b) := by
    rw [Finset.prod_filter, Fin.prod_univ_succ (n := 2 * k + 1)]
    simp only [ne_eq, not_true_eq_false, if_false, one_mul, Fin.succ_ne_zero, not_false_eq_true,
      if_true]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
  rw [h1, h2, ← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ.filter (fun b : Fin (2 * k + 2) => b ≠ 0)) (fun b => J.1 b < b),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  · ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      exact absurd h (Fin.not_lt_zero _)
    · exact fun h => h.2
  · ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Fin.pos_iff_ne_zero.1 h1, h2.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Fin.pos_iff_ne_zero.2 h1, lt_of_le_of_ne h2 (hne b).symm⟩

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- **Proof of (v)(b)** of `q_pow2_leading.md`: `s_i^q = 0` in `B`. -/
theorem y_pow_eq_zero (q d : ℕ) (i : Fin d) : Tight.y F (q + 1) i ^ q = 0 := by
  rw [Tight.y, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, by simp⟩

/-- **(v)(b) (the leading forms)** of `q_pow2_leading.md`: for `q = 2^v` with `v ≥ 1` and every
matching `J`, the class of `L_J` in `B = Peel.C F (q + 1) (2k + 1)` is `Y_d · Ē_J`, where `Ē_J` is
the class of `E_J` in `B` and `Y_d = s_1 ⋯ s_d` (`ColOne.Ym`). -/
theorem mk_LJ {v : ℕ} (hv : 1 ≤ v) {k : ℕ} (J : BallotBound.Matching k) :
    Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (LJ F (2 ^ v) J) =
      ColOne.Ym F (2 ^ v) (2 * k + 1) *
        Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (EJ F (2 ^ v) J) := by
  set y : Fin (2 * k + 1) → Peel.C F (2 ^ v + 1) (2 * k + 1) := Tight.y F (2 ^ v + 1) with hy
  set S := Finset.univ.filter (fun a : Fin (2 * k + 2) => 0 < a ∧ a < J.1 a)
  have h2 := two_eq_zero_C (F := F) (2 ^ v + 1) (2 * k + 1)
  have h0 : (0 : Fin (2 * k + 2)) < J.1 0 := Fin.pos_iff_ne_zero.2 (J.2 0).1
  -- the product over the `k + 1` pairs splits off the pair `{0, J(0)}`
  have hsplit : Finset.univ.filter (fun a : Fin (2 * k + 2) => a < J.1 a) = insert 0 S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, S]
    constructor
    · intro h
      rcases eq_or_ne a 0 with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr ⟨Fin.pos_iff_ne_zero.2 ha, h⟩
    · rintro (rfl | ⟨-, h⟩)
      · exact h0
      · exact h
  have h0S : (0 : Fin (2 * k + 2)) ∉ S := by simp [S]
  have hY : ColOne.Ym F (2 ^ v) (2 * k + 1) =
      (y (TheoremB.idx (J.1 0)) * ∏ a ∈ S, y (TheoremB.idx (J.1 a))) *
        ∏ a ∈ S, y (TheoremB.idx a) := by
    rw [ColOne.Ym, ← prod_pairs_eq J y, hsplit, Finset.prod_insert h0S]
  have hE : Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (EJ F (2 ^ v) J) =
      ∏ a ∈ S, ColOne.Dab (2 ^ v) (y (TheoremB.idx a)) (y (TheoremB.idx (J.1 a))) := by
    rw [EJ, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [ColOne.map_Dab]
    rfl
  have hL : Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (LJ F (2 ^ v) J) =
      y (TheoremB.idx (J.1 0)) *
        ∏ a ∈ S, (y (TheoremB.idx (J.1 a)) *
          (y (TheoremB.idx a) + y (TheoremB.idx (J.1 a))) ^ (2 ^ v - 1)) := by
    rw [LJ, hsplit, Finset.prod_insert h0S, Finset.prod_mul_distrib, map_mul, map_mul, map_prod,
      map_prod]
    simp only [map_pow, map_add]
    rw [mul_assoc]
    rfl
  have hfac : ∀ a ∈ S, y (TheoremB.idx (J.1 a)) *
      (y (TheoremB.idx a) + y (TheoremB.idx (J.1 a))) ^ (2 ^ v - 1) =
        y (TheoremB.idx a) * y (TheoremB.idx (J.1 a)) *
          ColOne.Dab (2 ^ v) (y (TheoremB.idx a)) (y (TheoremB.idx (J.1 a))) :=
    fun a _ => mul_add_pow_of_two_eq_zero h2 hv _ _ (y_pow_eq_zero _ _ _)
  rw [hL, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hY, hE]
  ring

end Leading

end Pow2

end
