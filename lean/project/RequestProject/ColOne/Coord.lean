module

public import RequestProject.ColPairs.Main
public import RequestProject.TheoremB.Main

/-!
# The coordinate `y = t − t^{−1}` in a box ring at the point `1` (`q_col_one.md`, Lemma 2.3)

This file formalizes the **Setting** ("Box rings at the point 1") and **Lemma 2.3 (local form)** of
`q_col_one.md`.

Conventions (reused unchanged from the earlier files):
* `S : ColSplit.ColSetting F` is the Setting of `q_col_splitting.md` (`F` of characteristic `p`,
  `q = p^v`); the extra hypothesis `p ≠ 2` of the Setting of `q_col_one.md` is the hypothesis
  `hp : S.p ≠ 2`;
* the box rings `B(W)` are `B.Box W` for `B : ColTensor.BoxSetting F d` (`q_col_tensor.md`); a box
  "at the point `1`" is expressed by the hypothesis `∀ s : W, B.c s = 1`, and its exponent is
  `S.q` (hypothesis `B.q = S.q`);
* the ring `B_n = F[y_1, …, y_n]/(y_i^q)` is `Peel.C F (B.q + 1) n` (the ring `C_n` of
  `q_peeling_lemma.md` with `q + 1` in place of `q`), exactly as in `q_col_pairs.md`
  (`ColPairs.coordEquiv`); its variable `y_i` is the class of `X i`;
* inverses in rings are Mathlib's `Ring.inverse` (the inverse on units), as in `ColPairs`.
-/

@[expose] public section

open MvPolynomial

namespace ColOne

open ColSplit ColTensor

variable {F : Type*} [Field F]

/-! ### Consequences of `p ≠ 2` -/

section Setting

variable (S : ColSetting F)

/-- **Setting** of `q_col_one.md`: Frobenius, `(a + b)^q = a^q + b^q` in every commutative
`F`-algebra (`F` has characteristic `p` and `q = p^v`). -/
theorem add_pow_q {A : Type*} [CommRing A] [Algebra F A] (a b : A) :
    (a + b) ^ S.q = a ^ S.q + b ^ S.q := by
  haveI := S.charP
  haveI : Fact S.p.Prime := ⟨S.hp⟩
  rcases subsingleton_or_nontrivial A with h | h
  · exact Subsingleton.elim _ _
  · haveI : FaithfulSMul F A :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A).injective
    haveI := charP_of_injective_algebraMap' F (A := A) S.p
    exact add_pow_char_pow a b S.p S.v

/-- **Setting** of `q_col_one.md`: Frobenius, `(a − b)^q = a^q − b^q` in every commutative
`F`-algebra. -/
theorem sub_pow_q {A : Type*} [CommRing A] [Algebra F A] (a b : A) :
    (a - b) ^ S.q = a ^ S.q - b ^ S.q := by
  have := add_pow_q S (a - b) b
  rw [sub_add_cancel] at this
  rw [this]; ring

variable {S}

/-- **Setting** of `q_col_one.md`: `p ≠ 2`, so `q` is odd. -/
theorem odd_q (hp : S.p ≠ 2) : Odd S.q := by
  have hpo : Odd S.p := S.hp.odd_of_ne_two hp
  exact hpo.pow

/-- **Setting** of `q_col_one.md`: `p ≠ 2`, so `q ≥ 3`. -/
theorem three_le_q (hp : S.p ≠ 2) : 3 ≤ S.q := by
  have h2 := S.hp.two_le
  have h3 : 3 ≤ S.p := by omega
  calc 3 ≤ S.p := h3
    _ = S.p ^ 1 := (pow_one _).symm
    _ ≤ S.p ^ S.v := Nat.pow_le_pow_right S.hp.pos S.one_le_v

/-- **Setting** of `q_col_one.md`: `h = (q − 1)/2 ≥ 1` (as `q ≥ 3`). -/
theorem one_le_h (hp : S.p ≠ 2) : 1 ≤ (S.q - 1) / 2 := by
  have := three_le_q hp; omega

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `2 ≠ 0` in `F`, as `p ≠ 2`. -/
theorem two_ne_zero' (hp : S.p ≠ 2) : (2 : F) ≠ 0 := by
  haveI := S.charP
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F S.p] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 h')

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `2` is a unit of every `F`-algebra (`p ≠ 2`). -/
theorem isUnit_two (hp : S.p ≠ 2) {A : Type*} [CommRing A] [Algebra F A] : IsUnit (2 : A) := by
  rw [← map_ofNat (algebraMap F A) 2]
  exact (Ne.isUnit (two_ne_zero' hp)).map _

end Setting

/-! ### The inverse of `t ↦ t − t^{−1}` on `1 +` nilpotents -/

section Tau

variable {A : Type*} [CommRing A] [Algebra F A]

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`: the explicit inverse of `t ↦ y = t − t^{−1}`:
`τ(y) := y/2 + (1 + y²/4)^{(q+1)/2}`.  (When `y^q = 0` and `q` is odd, `(1 + y²/4)^{(q+1)/2}` is
the square root `√(1 + y²/4)` congruent to `1`, so `τ(y) = (y + √(y² + 4))/2` is the root of
`t² − y t − 1` congruent to `1`.) -/
noncomputable def tau (F : Type*) [Field F] [Algebra F A] (q : ℕ) (y : A) : A :=
  algebraMap F A 2⁻¹ * y + (1 + algebraMap F A 4⁻¹ * y ^ 2) ^ ((q + 1) / 2)

variable {S : ColSetting F}

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`: if `y^q = 0` then `τ(y)·(τ(y) − y) = 1`, i.e.
`τ(y)` is a unit with `τ(y) − τ(y)^{−1} = y`. -/
theorem tau_mul (hp : S.p ≠ 2) {y : A} (hy : y ^ S.q = 0) :
    tau F S.q y * (tau F S.q y - y) = 1 := by
  have hh : algebraMap F A 2⁻¹ * algebraMap F A 2⁻¹ = algebraMap F A 4⁻¹ := by
    have : (2 : F)⁻¹ * 2⁻¹ = 4⁻¹ := by rw [← mul_inv]; norm_num
    rw [← map_mul, this]
  set h := algebraMap F A 2⁻¹
  set z := algebraMap F A 4⁻¹ * y ^ 2
  set w := (1 + z) ^ ((S.q + 1) / 2)
  have h2 := two_ne_zero' (F := F) hp
  have hodd := odd_q hp
  have hw : w ^ 2 = 1 + z := by
    have e : 2 * ((S.q + 1) / 2) = S.q + 1 := by obtain ⟨k, hk⟩ := hodd; omega
    rw [← pow_mul, mul_comm, e, pow_succ, add_pow_q S, one_pow]
    have : z ^ S.q = 0 := by
      rw [mul_pow, show y ^ 2 = y * y by ring, mul_pow, hy, zero_mul, mul_zero]
    rw [this, add_zero, one_mul]
  have hh2 : h + h = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ h2, map_one]
  show (h * y + w) * (h * y + w - y) = 1
  linear_combination hw + (w * y + y ^ 2 * h) * hh2 - y ^ 2 * hh

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`: if `y^q = 0` then `(τ(y) − 1)^q = 0`. -/
theorem tau_sub_one_pow {y : A} (hy : y ^ S.q = 0) :
    (tau F S.q y - 1) ^ S.q = 0 := by
  have hz : (algebraMap F A 4⁻¹ * y ^ 2) ^ S.q = 0 := by
    rw [mul_pow, show y ^ 2 = y * y by ring, mul_pow, hy, zero_mul, mul_zero]
  have e : tau F S.q y - 1 =
      algebraMap F A 2⁻¹ * y + ((1 + algebraMap F A 4⁻¹ * y ^ 2) ^ ((S.q + 1) / 2) - 1) := by
    unfold tau; ring
  rw [e, add_pow_q S, sub_pow_q S, mul_pow, hy, mul_zero, zero_add, one_pow, ← pow_mul,
    mul_comm ((S.q + 1) / 2) S.q, pow_mul, add_pow_q S, one_pow, hz, add_zero, one_pow, sub_self]

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`: `τ` commutes with `F`-algebra maps. -/
theorem map_tau {A' : Type*} [CommRing A'] [Algebra F A'] (f : A →ₐ[F] A') (q : ℕ) (y : A) :
    f (tau F q y) = tau F q (f y) := by
  simp [tau, map_add, map_mul, map_pow, AlgHom.commutes]

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`: two roots `a`, `b` of `T² − yT − 1` with
`a + b − y` a unit are equal (`(a − b)(a + b − y) = 0`). -/
theorem eq_of_root {a b y : A} (ha : a * (a - y) = 1) (hb : b * (b - y) = 1)
    (hu : IsUnit (a + b - y)) : a = b := by
  have : (a - b) * (a + b - y) = 0 := by linear_combination ha - hb
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 this)

end Tau

/-! ### The coordinates `y_s` -/

section Box

variable {d : ℕ} (B : BoxSetting F d) (W : Finset (Fin d))

/-- **Setting** ("Box rings at the point 1") of `q_col_one.md`: `y_s := t_s − t_s^{−1} ∈ B(W)`. -/
noncomputable def yW (s : W) : B.Box W := B.t W s - Ring.inverse (B.t W s)

/-- **Setting** of `q_col_one.md` (and Lemma 2.4 (ii)): `Y_W := Π_{s ∈ W} y_s ∈ B(W)`. -/
noncomputable def YW : B.Box W := ∏ s : W, yW B W s

variable {B W}

/-- **Setting** ("Box rings at the point 1") of `q_col_one.md`: every `t_s` is a unit of `B(W)`
(it is `1` plus a nilpotent). -/
theorem isUnit_t (hc : ∀ s : W, B.c s = 1) (s : W) : IsUnit (B.t W s) := by
  have := ColPairs.Box.isUnit_t_sub B W (i := s) (r := 0) (by rw [hc s]; exact one_ne_zero)
  simpa using this

/-- **Setting** of `q_col_one.md`: `t_s − 1` is nilpotent in `B(W)` (`(t_s − 1)^q = 0`). -/
theorem t_sub_one_pow (hc : ∀ s : W, B.c s = 1) (s : W) : (B.t W s - 1) ^ B.q = 0 := by
  have := B.t_sub_pow W s
  rwa [hc s, map_one] at this

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `t_s + t_l = 2 + (t_s − 1) + (t_l − 1)` is a unit of
`B(W)` (here `s = l` is allowed). -/
theorem isUnit_t_add_t {S : ColSetting F} (hp : S.p ≠ 2) (hc : ∀ s : W, B.c s = 1) (s l : W) :
    IsUnit (B.t W s + B.t W l) := by
  have e : B.t W s + B.t W l = 2 + ((B.t W s - 1) + (B.t W l - 1)) := by ring
  rw [e]
  exact IsNilpotent.isUnit_add_left_of_commute
    (Commute.isNilpotent_add (Commute.all _ _) ⟨_, t_sub_one_pow hc s⟩ ⟨_, t_sub_one_pow hc l⟩)
    (isUnit_two hp) (Commute.all _ _)

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `y_s = (t_s − 1)·((t_s + 1)·t_s^{−1})`. -/
theorem yW_eq (hc : ∀ s : W, B.c s = 1) (s : W) :
    yW B W s = (B.t W s - 1) * ((B.t W s + 1) * Ring.inverse (B.t W s)) := by
  have h1 := Ring.mul_inverse_cancel _ (isUnit_t hc s)
  unfold yW
  linear_combination (-(B.t W s)) * h1

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `(t_s + 1)·t_s^{−1}` is a unit (`t_s + 1` is a unit
since `2 ≠ 0`). -/
theorem isUnit_factor {S : ColSetting F} (hp : S.p ≠ 2) (hc : ∀ s : W, B.c s = 1) (s : W) :
    IsUnit ((B.t W s + 1) * Ring.inverse (B.t W s)) := by
  refine IsUnit.mul ?_ (isUnit_t hc s).ringInverse
  have e2 : B.t W s + 1 = 2 + (B.t W s - 1) := by ring
  rw [e2]
  exact IsNilpotent.isUnit_add_left_of_commute ⟨_, t_sub_one_pow hc s⟩ (isUnit_two hp)
    (Commute.all _ _)

/-- **Proof of Lemma 2.3** of `q_col_one.md`: `y_s^q = 0` in `B(W)`. -/
theorem yW_pow (hc : ∀ s : W, B.c s = 1) (s : W) : yW B W s ^ B.q = 0 := by
  rw [yW_eq hc, mul_pow, t_sub_one_pow hc, zero_mul]

/-- **Lemma 2.3 (ii)** of `q_col_one.md`, first claim: for `s ∈ W`, `t_s − 1 = u_s·y_s` with `u_s`
a unit of `B(W)`. -/
theorem lemma23_ii_one {S : ColSetting F} (hp : S.p ≠ 2) (hc : ∀ s : W, B.c s = 1) (s : W) :
    ∃ u : (B.Box W)ˣ, B.t W s - 1 = u * yW B W s := by
  obtain ⟨v, hv⟩ := isUnit_factor hp hc s
  refine ⟨v⁻¹, ?_⟩
  rw [yW_eq hc, ← hv, mul_comm, mul_assoc, Units.mul_inv, mul_one]

/-- **Lemma 2.3 (ii)** of `q_col_one.md`, second claim: for `s, l ∈ W`,
`t_s t_l − 1 = u_{s,l}·(y_s + y_l)` with `u_{s,l}` a unit of `B(W)`.  (The file assumes `s ≠ l`;
the statement holds for all `s, l`, which is slightly more general.) -/
theorem lemma23_ii_two {S : ColSetting F} (hp : S.p ≠ 2) (hc : ∀ s : W, B.c s = 1) (s l : W) :
    ∃ u : (B.Box W)ˣ, B.t W s * B.t W l - 1 = u * (yW B W s + yW B W l) := by
  obtain ⟨v, hv⟩ := isUnit_t_add_t hp hc s l
  obtain ⟨ws, hws⟩ := isUnit_t hc s
  obtain ⟨wl, hwl⟩ := isUnit_t hc l
  refine ⟨ws * wl * v⁻¹, ?_⟩
  have h1 := Ring.mul_inverse_cancel _ (isUnit_t hc s)
  have h2 := Ring.mul_inverse_cancel _ (isUnit_t hc l)
  have h3 : (v : B.Box W) * ((v⁻¹ : (B.Box W)ˣ) : B.Box W) = 1 := Units.mul_inv v
  rw [hv] at h3
  unfold yW
  simp only [Units.val_mul, hws, hwl]
  linear_combination (↑v⁻¹ * B.t W l) * h1 + (↑v⁻¹ * B.t W s) * h2 +
    (1 - B.t W s * B.t W l) * h3

/-! ### Lemma 2.3 (i): the isomorphism `Ψ_e` -/

variable (S : ColSetting F)

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`, the map `Ψ_e : B_n → B(W)`, `y_i ↦ y_{e(i)}`
(well defined since `y_s^q = 0`). -/
noncomputable def psiFwd (hc : ∀ s : W, B.c s = 1) {n : ℕ} (e : Fin n ≃ W) :
    Peel.C F (B.q + 1) n →ₐ[F] B.Box W :=
  Ideal.Quotient.liftₐ _ (aeval fun i => yW B W (e i)) (by
    intro f hf
    have hle : Peel.powIdeal F (B.q + 1) n ≤
        RingHom.ker (aeval fun i => yW B W (e i) : MvPolynomial (Fin n) F →ₐ[F] _) := by
      rw [Peel.powIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, yW_pow hc]
    exact hle hf)

/-- **Proof of Lemma 2.3 (i)** of `q_col_one.md`, the inverse map `B(W) → B_n`,
`t_s ↦ τ(y_{e^{−1}(s)})`. -/
noncomputable def psiBwd (hq : B.q = S.q) (hc : ∀ s : W, B.c s = 1) {n : ℕ}
    (e : Fin n ≃ W) : B.Box W →ₐ[F] Peel.C F (B.q + 1) n :=
  B.boxLift W (fun s => tau F S.q (Ideal.Quotient.mk _ (X (e.symm s)))) (fun s => by
    rw [hc s, map_one, hq]
    exact tau_sub_one_pow (by rw [← hq]; exact ColPairs.C_X_pow B.q n _))

/-- **Lemma 2.3 (i)** of `q_col_one.md`: for a box ring `B(W)` at the point `1` (with exponent `q`,
`p ≠ 2`) and a bijection `e : [n] → W`, the `F`-algebra isomorphism
`Ψ_e : B_n = F[y_1, …, y_n]/(y_i^q) → B(W)` with `Ψ_e(y_i) = y_{e(i)} = t_{e(i)} − t_{e(i)}^{−1}`
(see `Psi_X`). -/
noncomputable def Psi (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = 1) {n : ℕ}
    (e : Fin n ≃ W) : Peel.C F (B.q + 1) n ≃ₐ[F] B.Box W :=
  AlgEquiv.ofAlgHom (psiFwd hc e) (psiBwd S hq hc e)
    (B.box_algHom_ext fun s => by
      have hX : psiFwd hc e (Ideal.Quotient.mk _ (X (e.symm s))) = yW B W s := by
        simp [psiFwd]
      simp only [AlgHom.comp_apply, psiBwd, BoxSetting.boxLift_t, AlgHom.id_apply, map_tau, hX]
      have hy : yW B W s ^ S.q = 0 := by rw [← hq]; exact yW_pow hc s
      have h1 := Ring.mul_inverse_cancel _ (isUnit_t hc s)
      symm
      refine eq_of_root (y := yW B W s) (by unfold yW; simpa using h1) (tau_mul hp hy) ?_
      have e1 : B.t W s + tau F S.q (yW B W s) - yW B W s =
          2 + ((B.t W s - 1) + ((tau F S.q (yW B W s) - 1) - yW B W s)) := by ring
      rw [e1]
      refine IsNilpotent.isUnit_add_left_of_commute ?_ (isUnit_two hp) (Commute.all _ _)
      refine Commute.isNilpotent_add (Commute.all _ _) ⟨_, t_sub_one_pow hc s⟩ ?_
      exact Commute.isNilpotent_sub (Commute.all _ _) ⟨_, tau_sub_one_pow hy⟩ ⟨_, hy⟩)
    (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun m => by
      have hy : (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n) (X m)) ^ S.q = 0 := by
        rw [← hq]; exact ColPairs.C_X_pow B.q n m
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
      rw [show psiFwd hc e (Ideal.Quotient.mk _ (X m)) = yW B W (e m) by simp [psiFwd]]
      have hb : psiBwd S hq hc e (B.t W (e m)) =
          tau F S.q (Ideal.Quotient.mk _ (X m)) := by simp [psiBwd]
      unfold yW
      rw [map_sub, ColPairs.map_ringInverse _ (isUnit_t hc (e m)), hb]
      have h := tau_mul hp hy
      have hu : IsUnit (tau F S.q (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n) (X m))) :=
        IsUnit.of_mul_eq_one _ h
      have h2 := Ring.inverse_mul_cancel _ hu
      linear_combination (Ring.inverse (tau F S.q
        (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n) (X m)))) * h -
        (tau F S.q (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n) (X m)) -
          (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n) (X m))) * h2))

/-- **Lemma 2.3 (i)** of `q_col_one.md`: `Ψ_e(y_i) = y_{e(i)}`. -/
@[simp] theorem Psi_X (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = 1) {n : ℕ}
    (e : Fin n ≃ W) (i : Fin n) :
    Psi S hp hq hc e (Ideal.Quotient.mk _ (X i)) = yW B W (e i) := by
  simp [Psi, psiFwd]

/-- **Lemma 2.3 (i)** of `q_col_one.md`, as one statement: for a box ring `B(W)` at the point `1`
(exponent `q`, `p ≠ 2`), `n := |W|`, and any bijection `e : [n] → W`, there is an `F`-algebra
isomorphism `Ψ_e : B_n → B(W)` with `Ψ_e(y_i) = y_{e(i)}` for every `i`. -/
theorem lemma23_i (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = 1)
    (e : Fin W.card ≃ W) :
    ∃ Ψ : Peel.C F (B.q + 1) W.card ≃ₐ[F] B.Box W,
      ∀ i, Ψ (Ideal.Quotient.mk _ (X i)) = yW B W (e i) :=
  ⟨Psi S hp hq hc e, Psi_X S hp hq hc e⟩

end Box

end ColOne

end
