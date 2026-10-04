module

public import RequestProject.EvenMinus.Main
public import RequestProject.Pow2.Main
public import RequestProject.EvenOne.Theta

/-!
# Part A of `q_even_block_one.md`: the box at the point `1` at the prime `2` is a group algebra

* (A1) `EvenOne.A1`, `EvenOne.A1_of_two_eq_zero`, `EvenOne.A1_S`: in characteristic `2`, for
  `q = 2^v`, `(u − 1)^{q−1} = ColSurv.phi q u` and `(u − 1)^q = u^q − 1` (from
  `Pow2.phi_two_pow`).
* (A2) `EvenOne.PhiE`, `EvenOne.A2`: for `S.p = 2`, `W = WS S c 1` and a bijection
  `e : Fin n ≃ W`, the `F`-algebra isomorphism `Φ_e : GA F n S.q ≃ₐ[F] B(W)`,
  `Φ_e (mk (X i)) = t_{e i}`.
-/

@[expose] public section

open MvPolynomial

namespace EvenOne

open ColSplit ColSurv ColComp ColTensor ColDecomp EvenBlocks

variable {F : Type*} [Field F]

/-! ### (A1) -/

/-- **Part A, (A1)** of `q_even_block_one.md`, in the slightly more general form where only
`2 = 0` in `A` is assumed (instead of `CharP A 2`), and for every `v` (also `v = 0`):
`(u − 1)^{q−1} = phi q u` and `(u − 1)^q = u^q − 1` for `q = 2^v`. -/
theorem A1_of_two_eq_zero {A : Type*} [CommRing A] (h2 : (2 : A) = 0) (v : ℕ) (u : A) :
    (u - 1) ^ (2 ^ v - 1) = phi (2 ^ v) u ∧ (u - 1) ^ (2 ^ v) = u ^ (2 ^ v) - 1 := by
  have hpm : u - 1 = u + 1 := by linear_combination -h2
  have h1 : (u - 1) ^ (2 ^ v - 1) = phi (2 ^ v) u := by
    rw [Pow2.phi_two_pow_of_two_eq_zero h2, hpm]
  refine ⟨h1, ?_⟩
  calc (u - 1) ^ (2 ^ v) = (u - 1) * (u - 1) ^ (2 ^ v - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
    _ = (u - 1) * phi (2 ^ v) u := by rw [h1]
    _ = u ^ (2 ^ v) - 1 := by rw [phi, mul_geom_sum]

/-- **Part A, (A1)** of `q_even_block_one.md`: in every commutative ring `A` of characteristic `2`
and for `q = 2^v`: `(u − 1)^{q−1} = ColSurv.phi q u` and `(u − 1)^q = u^q − 1`. (The file assumes
`v ≥ 1`; the statement holds for every `v`.) -/
theorem A1 {A : Type*} [CommRing A] [CharP A 2] (v : ℕ) (u : A) :
    (u - 1) ^ (2 ^ v - 1) = phi (2 ^ v) u ∧ (u - 1) ^ (2 ^ v) = u ^ (2 ^ v) - 1 :=
  A1_of_two_eq_zero CharTwo.two_eq_zero v u

section Setting

variable (S : ColSetting F)

/-- **Part A** of `q_even_block_one.md` (setting): if `S.p = 2`, then `S.q = 2 ^ S.v`. -/
theorem q_eq_two_pow (hp : S.p = 2) : S.q = 2 ^ S.v := by
  unfold ColSetting.q; rw [hp]

/-- **Part A** of `q_even_block_one.md` (setting): if `S.p = 2`, then `CharP F 2`. -/
theorem charP_two (hp : S.p = 2) : CharP F 2 := by
  have := S.charP; rw [hp] at this; exact this

/-- **Part A** of `q_even_block_one.md` (setting): if `S.p = 2`, then `2 = 0` in every
`F`-algebra. -/
theorem two_eq_zero_alg (hp : S.p = 2) {A : Type*} [CommRing A] [Algebra F A] : (2 : A) = 0 := by
  haveI := charP_two S hp
  have h : (2 : F) = 0 := CharTwo.two_eq_zero
  calc (2 : A) = algebraMap F A 2 := (map_ofNat _ 2).symm
    _ = 0 := by rw [h, map_zero]

/-- **Part A, (A1)** of `q_even_block_one.md`, for a setting with `S.p = 2` and in every
`F`-algebra `A`: `(u − 1)^{q−1} = phi q u` and `(u − 1)^q = u^q − 1`, `q = S.q`. -/
theorem A1_S (hp : S.p = 2) {A : Type*} [CommRing A] [Algebra F A] (u : A) :
    (u - 1) ^ (S.q - 1) = phi S.q u ∧ (u - 1) ^ S.q = u ^ S.q - 1 := by
  rw [q_eq_two_pow S hp]
  exact A1_of_two_eq_zero (two_eq_zero_alg S hp) _ u

end Setting

/-! ### (A2) -/

/-- **Part A, (A2)** of `q_even_block_one.md` (proof; universal property of `GA`): two `F`-algebra
maps out of `GA F n m` agreeing on the classes of the variables are equal. -/
theorem ga_algHom_ext {n m : ℕ} {B : Type*} [CommRing B] [Algebra F B]
    {f g : GA F n m →ₐ[F] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simpa using h i

variable (S : ColSetting F) {k : ℕ}

/-- **Part A, (A2)** of `q_even_block_one.md` (proof): the map `GA F n q → B(W)`,
`X i ↦ t_{e i}` (well defined: `t^q − 1 = (t − 1)^q = 0` in `B(W)` by (A1), every `c_s` on
`W = WS S c 1` being `1`). -/
noncomputable def gaToBox (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) : GA F n S.q →ₐ[F] (boxS S c).Box (WS S c 1) :=
  Ideal.Quotient.liftₐ (gaIdeal F n S.q) (aeval fun i => (boxS S c).t _ (e i)) (by
    intro a ha
    have hle : gaIdeal F n S.q ≤ RingHom.ker
        (aeval (fun i => (boxS S c).t _ (e i)) : MvPolynomial (Fin n) F →ₐ[F] _) := by
      rw [gaIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, aeval_X, map_one]
      have h : ((boxS S c).t _ (e i) - algebraMap F _ ((boxS S c).c (e i))) ^ S.q = 0 :=
        (boxS S c).t_sub_pow _ _
      rwa [EvenMinus.boxS_c_WS S c 1 (e i), map_one, (A1_S S hp _).2] at h
    exact hle ha)

/-- **Part A, (A2)** of `q_even_block_one.md` (proof): `gaToBox (X i) = t_{e i}`. -/
@[simp] theorem gaToBox_X (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) (i : Fin n) :
    gaToBox S hp c e (Ideal.Quotient.mk _ (X i)) = (boxS S c).t _ (e i) := by
  simp [gaToBox]

/-- **Part A, (A2)** of `q_even_block_one.md` (proof): the map `B(W) → GA F n q`,
`t_s ↦ X (e⁻¹ s)` (well defined: `(X − 1)^q = X^q − 1 = 0` in `GA` by (A1)). -/
noncomputable def boxToGA (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) : (boxS S c).Box (WS S c 1) →ₐ[F] GA F n S.q :=
  (boxS S c).boxLift (WS S c 1) (fun s => Ideal.Quotient.mk _ (X (e.symm s))) (fun s => by
    rw [EvenMinus.boxS_c_WS S c 1 s, map_one]
    change (_ - 1) ^ S.q = 0
    rw [(A1_S S hp _).2, ← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨_, rfl⟩)

/-- **Part A, (A2)** of `q_even_block_one.md` (proof): `boxToGA (t_s) = X (e⁻¹ s)`. -/
@[simp] theorem boxToGA_t (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) (s : WS S c 1) :
    boxToGA S hp c e ((boxS S c).t _ s) = Ideal.Quotient.mk _ (X (e.symm s)) := by
  simp [boxToGA]

/-- **Part A, (A2)** of `q_even_block_one.md`: for `S.p = 2`, `W = WS S c 1` and a bijection
`e : Fin n ≃ W`, the `F`-algebra isomorphism `Φ_e : ColSplit.GA F n S.q ≃ₐ[F] B(W)` with
`Φ_e (mk (X i)) = t_{e i}`. -/
noncomputable def PhiE (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) : GA F n S.q ≃ₐ[F] (boxS S c).Box (WS S c 1) :=
  AlgEquiv.ofAlgHom (gaToBox S hp c e) (boxToGA S hp c e)
    ((boxS S c).box_algHom_ext fun s => by simp)
    (ga_algHom_ext fun i => by simp)

/-- **Part A, (A2)** of `q_even_block_one.md`: `Φ_e (mk (X i)) = t_{e i}`. -/
@[simp] theorem PhiE_X (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) (i : Fin n) :
    PhiE S hp c e (Ideal.Quotient.mk _ (X i)) = (boxS S c).t _ (e i) := by
  simp [PhiE]

/-- **Part A, (A2)** of `q_even_block_one.md`: `Φ_e⁻¹ (t_s) = mk (X (e⁻¹ s))`. -/
@[simp] theorem PhiE_symm_t (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ}
    (e : Fin n ≃ WS S c 1) (s : WS S c 1) :
    (PhiE S hp c e).symm ((boxS S c).t _ s) = Ideal.Quotient.mk _ (X (e.symm s)) := by
  simp [PhiE, AlgEquiv.ofAlgHom_symm]

/-- **Part A, (A2)** of `q_even_block_one.md`: if `S.p = 2` and `W := WS S c 1`, then for every
bijection `e : Fin n ≃ W` there is an `F`-algebra isomorphism
`Φ_e : ColSplit.GA F n S.q ≃ₐ[F] (boxS S c).Box W` with `Φ_e (mk (X i)) = t_{e i}`. -/
theorem A2 (hp : S.p = 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ} (e : Fin n ≃ WS S c 1) :
    ∃ Φ : GA F n S.q ≃ₐ[F] (boxS S c).Box (WS S c 1),
      ∀ i, Φ (Ideal.Quotient.mk _ (X i)) = (boxS S c).t _ (e i) :=
  ⟨PhiE S hp c e, PhiE_X S hp c e⟩

end EvenOne

end
