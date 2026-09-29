module

public import RequestProject.ColDecomp.Main
public import RequestProject.BipInd.Main

/-!
# Changes of coordinates in a box ring (`q_col_pairs.md`, proof of Lemma 6.7 (i), (ii))

This file contains the ring-theoretic part of the **Proof** of Lemma 6.7 (i) and (ii) of
`q_col_pairs.md`, in a generic form: for a box ring `B(W)` of `q_col_tensor.md` all of whose points
`c_s` are `ζ` or `ζ^{−1}` (`ζ ≠ 0`), the new coordinates `x_s = ζ^{−1} t_s − 1` (where `c_s = ζ`) and
`z_s = (ζ t_s)^{−1} − 1` (where `c_s = ζ^{−1}`) satisfy `x_s^q = z_s^q = 0`, and any enumeration of `W`
gives an `F`-algebra isomorphism `F[y_1, …, y_n]/(y_i^q) ≅ B(W)` sending the variables to these
coordinates.  Inverses in rings are `Ring.inverse` (a total function, the inverse on units).
-/

@[expose] public section

open MvPolynomial

namespace ColPairs

open ColTensor

variable {F : Type*} [Field F]

/-- `Ring.inverse` commutes with ring homomorphisms on units (used in the **Proof** of Lemma 6.7 (i)
of `q_col_pairs.md` to compute the two composites). -/
theorem map_ringInverse {A B H : Type*} [CommRing A] [CommRing B] [FunLike H A B]
    [RingHomClass H A B] (f : H) {u : A} (hu : IsUnit u) :
    f (Ring.inverse u) = Ring.inverse (f u) := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit]
  have h : f (v : A) = ((Units.map (f : A →* B) v : Bˣ) : B) := rfl
  rw [h, Ring.inverse_unit]
  rfl

/-- `Ring.inverse (Ring.inverse u) = u` for a unit `u` (**Proof** of Lemma 6.7 (i), (ii) of
`q_col_pairs.md`). -/
theorem ringInverse_ringInverse {A : Type*} [CommRing A] {u : A} (hu : IsUnit u) :
    Ring.inverse (Ring.inverse u) = u := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]

namespace Box

variable {d : ℕ} (B : BoxSetting F d) (W : Finset (Fin d))

/-- **Proof** of Lemma 6.7 (ii) of `q_col_pairs.md`: `t_s − c_s` is nilpotent in `B(W)`. -/
theorem isNilpotent_t_sub (i : W) : IsNilpotent (B.t W i - algebraMap F _ (B.c i)) :=
  ⟨B.q, B.t_sub_pow W i⟩

/-- **Proof** of Lemma 6.7 (ii) of `q_col_pairs.md`: for `r ≠ c_s`, `t_s − r` is a unit of `B(W)`
(a non-zero constant `c_s − r` plus the nilpotent `t_s − c_s`). -/
theorem isUnit_t_sub {i : W} {r : F} (h : B.c i ≠ r) : IsUnit (B.t W i - algebraMap F _ r) := by
  have e : B.t W i - algebraMap F _ r =
      algebraMap F _ (B.c i - r) + (B.t W i - algebraMap F _ (B.c i)) := by
    rw [map_sub]; ring
  rw [e]
  exact (isNilpotent_t_sub B W i).isUnit_add_left_of_commute
    ((Ne.isUnit (sub_ne_zero.2 h)).map _) (Commute.all _ _)

/-- **Setting** of `q_col_pairs.md` (`t_l` is a unit): if `c_s ≠ 0` and `ζ ≠ 0`, then `ζ t_s` is a
unit of `B(W)`. -/
theorem isUnit_smul_t {i : W} {ζ : F} (hζ : ζ ≠ 0) (h : B.c i ≠ 0) :
    IsUnit (algebraMap F _ ζ * B.t W i) := by
  refine ((Ne.isUnit hζ).map (algebraMap F (B.Box W))).mul ?_
  simpa using isUnit_t_sub B W h

end Box

/-! ### The generic change of coordinates -/

section Coord

variable {d : ℕ} (B : BoxSetting F d) (W : Finset (Fin d)) (P : Fin d → Prop) [DecidablePred P]
  (ζ : F)

/-- **Setting** of `q_col_pairs.md`: the new coordinate at `s ∈ W`: `x_s := ζ^{−1} t_s − 1` if `P s`
(the case `c_s = ζ`, i.e. `s ∈ A^*`), and `z_s := (ζ t_s)^{−1} − 1` otherwise (the case
`c_s = ζ^{−1}`, i.e. `s ∈ B^*`). -/
noncomputable def yC (j : W) : B.Box W :=
  if P j then algebraMap F _ ζ⁻¹ * B.t W j - 1
  else Ring.inverse (algebraMap F _ ζ * B.t W j) - 1

/-- **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`, backward direction: the image of `t_s` under
the inverse map, as a function of the coordinate `y`: `ζ(1 + y)` if `P s`, and
`ζ^{−1}(1 + y)^{−1}` otherwise. -/
noncomputable def wC {C : Type*} [CommRing C] [Algebra F C] (j : Fin d) (y : C) : C :=
  if P j then algebraMap F C ζ * (1 + y) else algebraMap F C ζ⁻¹ * Ring.inverse (1 + y)

variable {B W P ζ}

/-- **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`: `x_s^q = 0` and `z_s^q = 0` in `B(W)`. -/
theorem yC_pow (hζ : ζ ≠ 0) (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) (j : W) :
    yC B W P ζ j ^ B.q = 0 := by
  have hq := B.t_sub_pow W j
  unfold yC
  split_ifs with h
  · have hcj : B.c j = ζ := by rw [hc j, if_pos h]
    rw [hcj] at hq
    have e : algebraMap F (B.Box W) ζ⁻¹ * B.t W j - 1 =
        algebraMap F _ ζ⁻¹ * (B.t W j - algebraMap F _ ζ) := by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hζ, map_one]
    rw [e, mul_pow, hq, mul_zero]
  · have hcj : B.c j = ζ⁻¹ := by rw [hc j, if_neg h]
    rw [hcj] at hq
    have hu : IsUnit (algebraMap F (B.Box W) ζ * B.t W j) :=
      Box.isUnit_smul_t B W hζ (by rw [hcj]; exact inv_ne_zero hζ)
    have e : Ring.inverse (algebraMap F (B.Box W) ζ * B.t W j) - 1 =
        -(Ring.inverse (algebraMap F (B.Box W) ζ * B.t W j) * algebraMap F _ ζ) *
          (B.t W j - algebraMap F _ ζ⁻¹) := by
      have h1 := Ring.inverse_mul_cancel _ hu
      have h2 : algebraMap F (B.Box W) ζ * algebraMap F _ ζ⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hζ, map_one]
      linear_combination h1 - Ring.inverse (algebraMap F (B.Box W) ζ * B.t W j) * h2
    rw [e, mul_pow, hq, mul_zero]

/-- **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`: the images `ζ(1 + y)` and
`ζ^{−1}(1 + y)^{−1}` of the inverse map satisfy the relations `(· − c_s)^q = 0` when `y^q = 0`. -/
theorem wC_rel {C : Type*} [CommRing C] [Algebra F C]
    (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) (j : W) {y : C} (hy : y ^ B.q = 0) :
    (wC P ζ j.1 y - algebraMap F C (B.c j)) ^ B.q = 0 := by
  unfold wC
  split_ifs with h
  · rw [hc j, if_pos h]
    have e : algebraMap F C ζ * (1 + y) - algebraMap F C ζ = algebraMap F C ζ * y := by ring
    rw [e, mul_pow, hy, mul_zero]
  · rw [hc j, if_neg h]
    have hu : IsUnit (1 + y) := IsNilpotent.isUnit_one_add ⟨_, hy⟩
    have e : algebraMap F C ζ⁻¹ * Ring.inverse (1 + y) - algebraMap F C ζ⁻¹ =
        -(algebraMap F C ζ⁻¹ * Ring.inverse (1 + y)) * y := by
      have h1 := Ring.inverse_mul_cancel _ hu
      linear_combination (algebraMap F C ζ⁻¹) * h1
    rw [e, mul_pow, hy, mul_zero]

variable (B W P ζ)

/-- The relation `y_m^q = 0` in `F[y_1, …, y_n]/(y_i^q)` (the ring `R_{α,β}` of `q_bip_setting.md`
is of this form); used in the **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`. -/
theorem C_X_pow (q n : ℕ) (m : Fin n) :
    (Ideal.Quotient.mk (Peel.powIdeal F (q + 1) n) (X m) : Peel.C F (q + 1) n) ^ q = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have := Ideal.subset_span (α := MvPolynomial (Fin n) F)
    (s := Set.range fun i : Fin n => (X i ^ (q + 1 - 1) : MvPolynomial (Fin n) F)) ⟨m, rfl⟩
  simpa using this

/-- **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`, forward map: for an enumeration
`e : [n] → W`, the `F`-algebra map `F[y_1, …, y_n]/(y_i^q) → B(W)`, `y_m ↦ (new coordinate at
e(m))`. -/
noncomputable def coordFwd (hζ : ζ ≠ 0) (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) {n : ℕ}
    (e : Fin n ≃ W) : Peel.C F (B.q + 1) n →ₐ[F] B.Box W :=
  Ideal.Quotient.liftₐ _ (aeval fun m => yC B W P ζ (e m)) (by
    intro f hf
    have hle : Peel.powIdeal F (B.q + 1) n ≤
        RingHom.ker (aeval fun m => yC B W P ζ (e m) : MvPolynomial (Fin n) F →ₐ[F] _) := by
      rw [Peel.powIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, yC_pow hζ hc]
    exact hle hf)

/-- **Proof** of Lemma 6.7 (i) of `q_col_pairs.md`, backward map: `B(W) → F[y_1, …, y_n]/(y_i^q)`,
`t_s ↦ ζ(1 + y_{e^{−1}(s)})` or `ζ^{−1}(1 + y_{e^{−1}(s)})^{−1}`. -/
noncomputable def coordBwd (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) {n : ℕ}
    (e : Fin n ≃ W) : B.Box W →ₐ[F] Peel.C F (B.q + 1) n :=
  B.boxLift W (fun j => wC P ζ j.1 (Ideal.Quotient.mk _ (X (e.symm j))))
    (fun j => wC_rel hc j (C_X_pow B.q n _))

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (generic form): for an enumeration `e : [n] → W`, the
`F`-algebra isomorphism `F[y_1, …, y_n]/(y_i^q) ≅ B(W)`, `y_m ↦ (new coordinate at e(m))`. -/
noncomputable def coordEquiv (hζ : ζ ≠ 0) (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) {n : ℕ}
    (e : Fin n ≃ W) : Peel.C F (B.q + 1) n ≃ₐ[F] B.Box W :=
  AlgEquiv.ofAlgHom (coordFwd B W P ζ hζ hc e) (coordBwd B W P ζ hc e)
    (B.box_algHom_ext fun j => by
      have hX : coordFwd B W P ζ hζ hc e (Ideal.Quotient.mk _ (X (e.symm j))) = yC B W P ζ j := by
        simp [coordFwd]
      simp only [AlgHom.comp_apply, coordBwd, BoxSetting.boxLift_t, AlgHom.id_apply]
      unfold wC
      split_ifs with h
      · rw [map_mul, map_add, hX, AlgHom.commutes, map_one, yC, if_pos h, add_sub_cancel,
          ← mul_assoc, ← map_mul, mul_inv_cancel₀ hζ, map_one, one_mul]
      · have hu : IsUnit (algebraMap F (B.Box W) ζ * B.t W j) :=
          Box.isUnit_smul_t B W hζ (by rw [hc j, if_neg h]; exact inv_ne_zero hζ)
        have hu' : IsUnit (1 + (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n)) (X (e.symm j))) :=
          IsNilpotent.isUnit_one_add ⟨_, C_X_pow B.q n _⟩
        rw [map_mul, map_ringInverse _ hu', map_add, hX, AlgHom.commutes, map_one, yC, if_neg h,
          add_sub_cancel, ringInverse_ringInverse hu, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hζ, map_one, one_mul])
    (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun m => by
      have hX : coordBwd B W P ζ hc e (B.t W (e m)) =
          wC P ζ (e m).1 (Ideal.Quotient.mk _ (X m)) := by
        simp [coordBwd]
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
      rw [show coordFwd B W P ζ hζ hc e (Ideal.Quotient.mk _ (X m)) = yC B W P ζ (e m) by
        simp [coordFwd]]
      unfold yC
      split_ifs with h
      · rw [map_sub, map_mul, hX, AlgHom.commutes, map_one, wC, if_pos h, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hζ, map_one, one_mul, add_sub_cancel_left]
      · have hu' : IsUnit (1 + (Ideal.Quotient.mk (Peel.powIdeal F (B.q + 1) n)) (X m)) :=
          IsNilpotent.isUnit_one_add ⟨_, C_X_pow B.q n _⟩
        have hu : IsUnit (algebraMap F (B.Box W) ζ * B.t W (e m)) :=
          Box.isUnit_smul_t B W hζ (by rw [hc (e m), if_neg h]; exact inv_ne_zero hζ)
        rw [map_sub, map_ringInverse _ hu, map_mul, hX, AlgHom.commutes, map_one, wC, if_neg h,
          ← mul_assoc, ← map_mul, mul_inv_cancel₀ hζ, map_one, one_mul,
          ringInverse_ringInverse hu', add_sub_cancel_left]))

/-- **Lemma 6.7 (i)** of `q_col_pairs.md` (generic form): the isomorphism sends `y_m` to the new
coordinate at `e(m)`. -/
@[simp] theorem coordEquiv_X (hζ : ζ ≠ 0) (hc : ∀ j : W, B.c j = if P j then ζ else ζ⁻¹) {n : ℕ}
    (e : Fin n ≃ W) (m : Fin n) :
    coordEquiv B W P ζ hζ hc e (Ideal.Quotient.mk _ (X m)) = yC B W P ζ (e m) := by
  simp [coordEquiv, coordFwd]

end Coord

end ColPairs

end
