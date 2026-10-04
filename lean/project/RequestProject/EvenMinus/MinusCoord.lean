module

public import RequestProject.ColOne.Main
public import RequestProject.EvenBlocks.Main
public import RequestProject.BipAny.Main

/-!
# Part M, (M1)–(M3) of `q_even_block_minus.md`: coordinates on the block of colour `−1`

* `EvenMinus.negBox B`: the box setting with the point `−c` (same exponent);
  `EvenMinus.negEquiv B W : B(W) ≃ B^−(W)`, `t ↦ −t` (the automorphism "`t ↦ −t`" of (M1)).
* (M1) `EvenMinus.PsiM`, `EvenMinus.lemmaM1`: for a box at the point `−1` (with `p ≠ 2`),
  `Ψ : F[y_1, …, y_n]/(y_i^q) ≅ B(W)` with `Ψ(y_i) = u − u^{−1}`, `u = −t_{e(i)}` — the composite
  of `ColOne.Psi` (Lemma 2.3 (i) at the point `1`) for `negBox B` with `negEquiv⁻¹`.
* (M2) `EvenMinus.lemmaM2`: `t_s − 1` is a unit, and `t_i t_l − 1 = (unit)·(y_i + y_l)`.
* (M3) `EvenMinus.lemmaM3`: `(a + b)^{q−1} = Σ_{u=0}^{q−1} (−1)^u a^u b^{q−1−u}` in every commutative
  `F`-algebra, in every characteristic `p` (`2` included); the right side is
  `ColOne.Dab (q + 1) a b`, the polynomial of `Tight.D F (q + 1)` (hence of
  `TheoremB.DIdeal F (q + 1)` and `Tight.VLam F (q + 1)`), see `EvenMinus.D_succ_eq`.
-/

@[expose] public section

open MvPolynomial

namespace EvenMinus

open ColSplit ColSurv ColTensor

variable {F : Type*} [Field F]

/-! ### The automorphism `t ↦ −t` -/

section NegBox

variable {d : ℕ} (B : BoxSetting F d)

/-- **Part M, (M1)** of `q_even_block_minus.md` (the automorphism `t ↦ −t`): the box setting
with the same exponent `q` and the point `−c` in place of `c`. -/
abbrev negBox : BoxSetting F d where
  q := B.q
  one_le_q := B.one_le_q
  c := fun i => -B.c i

variable (W : Finset (Fin d))

/-- **Part M, (M1)** of `q_even_block_minus.md` (proof): in `B^−(W)`, `(−t_s − c_s)^q = 0`. -/
theorem neg_t_sub_pow_negBox (i : W) :
    (-(negBox B).t W i - algebraMap F ((negBox B).Box W) (B.c i)) ^ B.q = 0 := by
  have h := (negBox B).t_sub_pow W i
  have e : -(negBox B).t W i - algebraMap F ((negBox B).Box W) (B.c i) =
      -((negBox B).t W i - algebraMap F _ ((negBox B).c i)) := by
    simp only [negBox, map_neg]; ring
  rw [e, neg_pow]
  exact mul_eq_zero_of_right _ h

/-- **Part M, (M1)** of `q_even_block_minus.md` (proof): in `B(W)`, `(−t_s − (−c_s))^q = 0`. -/
theorem neg_t_sub_pow (i : W) :
    (-B.t W i - algebraMap F (B.Box W) ((negBox B).c i)) ^ (negBox B).q = 0 := by
  have h := B.t_sub_pow W i
  have e : -B.t W i - algebraMap F (B.Box W) ((negBox B).c i) =
      -(B.t W i - algebraMap F _ (B.c i)) := by
    simp only [map_neg]; ring
  rw [e, neg_pow]
  exact mul_eq_zero_of_right _ h

/-- **Part M, (M1)** of `q_even_block_minus.md`: the `F`-algebra isomorphism
`B(W) ≃ B^−(W)`, `t_s ↦ −t_s` (the automorphism `t ↦ −t` taking the point `−1` to the point `1`). -/
noncomputable def negEquiv : B.Box W ≃ₐ[F] (negBox B).Box W :=
  AlgEquiv.ofAlgHom (B.boxLift W (fun s => -(negBox B).t W s) (neg_t_sub_pow_negBox B W))
    ((negBox B).boxLift W (fun s => -B.t W s) (neg_t_sub_pow B W))
    ((negBox B).box_algHom_ext fun s => by simp)
    (B.box_algHom_ext fun s => by simp)

/-- **Part M, (M1)** of `q_even_block_minus.md`: `negEquiv(t_s) = −t_s`. -/
@[simp] theorem negEquiv_t (s : W) : negEquiv B W (B.t W s) = -(negBox B).t W s := by
  simp [negEquiv]

/-- **Part M, (M1)** of `q_even_block_minus.md`: `negEquiv^{−1}(t_s) = −t_s`. -/
@[simp] theorem negEquiv_symm_t (s : W) :
    (negEquiv B W).symm ((negBox B).t W s) = -B.t W s := by
  simp [negEquiv, AlgEquiv.ofAlgHom_symm]

variable {B W}

/-- **Part M, (M1)** of `q_even_block_minus.md`: if every point of `W` is `−1`, then `negBox B`
is a box at the point `1`. -/
theorem negBox_c_eq_one (hc : ∀ s : W, B.c s = -1) : ∀ s : W, (negBox B).c s = 1 := by
  intro s
  simp [hc s]

variable (B W)

/-- **Part M, (M1)** of `q_even_block_minus.md`: the coordinate `y_s := u_s − u_s^{−1}` with
`u_s := −t_s` in `B(W)`. -/
noncomputable def yM (s : W) : B.Box W := -B.t W s - Ring.inverse (-B.t W s)

variable {B W}

/-- **Part M, (M1)** of `q_even_block_minus.md`: `negEquiv^{−1}` takes the coordinate
`t − t^{−1}` of `B^−(W)` (at the point `1`) to the coordinate `y = u − u^{−1}`, `u = −t`. -/
theorem negEquiv_symm_yW (hc : ∀ s : W, B.c s = -1) (s : W) :
    (negEquiv B W).symm (ColOne.yW (negBox B) W s) = yM B W s := by
  unfold ColOne.yW yM
  rw [map_sub, ColPairs.map_ringInverse _ (ColOne.isUnit_t (negBox_c_eq_one hc) s),
    negEquiv_symm_t]

/-! ### (M1) -/

variable (S : ColSetting F)

/-- **Part M, (M1)** of `q_even_block_minus.md`: for a box `B(W)` at the point `−1` (exponent
`q`, `p ≠ 2`) and a bijection `e : [n] → W`, the `F`-algebra isomorphism
`Ψ = negEquiv^{−1} ∘ Ψ_e : F[y_1, …, y_n]/(y_i^q) → B(W)` (`Ψ_e` from `ColOne.Psi` for
`negBox B`). -/
noncomputable def PsiM (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = -1) {n : ℕ}
    (e : Fin n ≃ W) : Peel.C F (B.q + 1) n ≃ₐ[F] B.Box W :=
  (ColOne.Psi (B := negBox B) S hp hq (negBox_c_eq_one hc) e).trans (negEquiv B W).symm

/-- **Part M, (M1)** of `q_even_block_minus.md`: `Ψ(y_i) = u − u^{−1}` with `u = −t_{e(i)}`. -/
@[simp] theorem PsiM_X (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = -1) {n : ℕ}
    (e : Fin n ≃ W) (i : Fin n) :
    PsiM S hp hq hc e (Ideal.Quotient.mk _ (X i)) = yM B W (e i) := by
  have h := ColOne.Psi_X (B := negBox B) S hp hq (negBox_c_eq_one hc) e i
  simp only [PsiM, AlgEquiv.trans_apply]
  erw [h]
  exact negEquiv_symm_yW hc _

/-- **Part M, (M1)** of `q_even_block_minus.md` (local form): for a box ring `B(W)` at the point
`−1` (exponent `q`, `p ≠ 2`) and any bijection `e : [n] → W` (for instance the increasing one,
`n = |W|`), there is an `F`-algebra isomorphism `Ψ : F[y_1, …, y_n]/(y_i^q) ≃ B(W)` with
`Ψ(y_i) = u − u^{−1}`, `u = −t_{e(i)}`. -/
theorem lemmaM1_box (hp : S.p ≠ 2) (hq : B.q = S.q) (hc : ∀ s : W, B.c s = -1) {n : ℕ}
    (e : Fin n ≃ W) :
    ∃ Ψ : Peel.C F (B.q + 1) n ≃ₐ[F] B.Box W, ∀ i,
      Ψ (Ideal.Quotient.mk _ (X i)) = -B.t W (e i) - Ring.inverse (-B.t W (e i)) :=
  ⟨PsiM S hp hq hc e, PsiM_X S hp hq hc e⟩

/-! ### (M2) -/

/-- **Part M, (M2)** of `q_even_block_minus.md` (local form): for a box ring `B(W)` at the point
`−1` with `p ≠ 2`: `t_s − 1` is a unit for every `s ∈ W`, and for `i, l ∈ W`,
`t_i t_l − 1 = (unit)·(y_i + y_l)` with `y = u − u^{−1}`, `u = −t` (the file assumes `i ≠ l`; the
statement holds for all `i, l`). -/
theorem lemmaM2_box (hp : S.p ≠ 2) (hc : ∀ s : W, B.c s = -1) :
    (∀ s : W, IsUnit (B.t W s - 1)) ∧
    ∀ i l : W, ∃ u : (B.Box W)ˣ, B.t W i * B.t W l - 1 = u * (yM B W i + yM B W l) := by
  have hne : (-1 : F) ≠ 1 := by
    intro h
    have h2 : (2 : F) = 0 := by linear_combination -h
    exact ColOne.two_ne_zero' (S := S) hp h2
  refine ⟨fun s => ?_, fun i l => ?_⟩
  · have := ColPairs.Box.isUnit_t_sub B W (i := s) (r := 1) (by rw [hc s]; exact hne)
    simpa using this
  · obtain ⟨u, hu⟩ := ColOne.lemma23_ii_two (S := S) hp (negBox_c_eq_one hc) i l
    refine ⟨Units.map ((negEquiv B W).symm : (negBox B).Box W →* B.Box W) u, ?_⟩
    have h := congrArg (negEquiv B W).symm hu
    rw [map_sub, map_mul, map_one, negEquiv_symm_t, negEquiv_symm_t, map_mul, map_add,
      negEquiv_symm_yW hc, negEquiv_symm_yW hc] at h
    rw [Units.coe_map]
    change _ = (negEquiv B W).symm (u : (negBox B).Box W) * _
    rw [← h]
    ring

end NegBox

/-! ### (M3) -/

/-- **Part M, (M3)** of `q_even_block_minus.md`: in characteristic `p` with `q = p^v` (every prime
`p`, `2` included), for all `a`, `b` in a commutative `F`-algebra:
`(a + b)^{q−1} = Σ_{u=0}^{q−1} (−1)^u a^u b^{q−1−u}`, and this sum is `ColOne.Dab (q + 1) a b`
(the divided difference of `Tight.D F (q + 1)`, used by `TheoremB.DIdeal F (q + 1)` and
`Tight.VLam F (q + 1)`). Proof: the binomial theorem and `BipAny.choose_pred_prime_pow`. -/
theorem lemmaM3 (S : ColSetting F) {A : Type*} [CommRing A] [Algebra F A] (a b : A) :
    (a + b) ^ (S.q - 1) = ∑ u ∈ Finset.range S.q, (-1) ^ u * a ^ u * b ^ (S.q - 1 - u) ∧
      ColOne.Dab (S.q + 1) a b = ∑ u ∈ Finset.range S.q, (-1) ^ u * a ^ u * b ^ (S.q - 1 - u) := by
  haveI := S.charP
  have hq1 : 1 ≤ S.q := Setting.one_le_q S
  have hch := BipAny.choose_pred_prime_pow F S.hp S.one_le_v (q := S.q) rfl
  refine ⟨?_, ?_⟩
  · rw [add_pow, show S.q - 1 + 1 = S.q by omega]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u ≤ S.q - 1 := by rw [Finset.mem_range] at hu; omega
    have hc : (((S.q - 1).choose u : ℕ) : A) = (-1) ^ u := by
      rw [← map_natCast (algebraMap F A), hch u hu', map_pow, map_neg, map_one]
    rw [hc]; ring
  · unfold ColOne.Dab
    rw [show S.q + 1 - 1 = S.q by omega]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show S.q + 1 - 2 - u = S.q - 1 - u by omega]

/-- **Part M, (M3)** of `q_even_block_minus.md`: `(a + b)^{q−1} = ColOne.Dab (q + 1) a b` in every
commutative `F`-algebra, every characteristic. -/
theorem add_pow_eq_Dab (S : ColSetting F) {A : Type*} [CommRing A] [Algebra F A] (a b : A) :
    (a + b) ^ (S.q - 1) = ColOne.Dab (S.q + 1) a b := by
  rw [(lemmaM3 S a b).1, (lemmaM3 S a b).2]

/-- **Part M, (M3)** of `q_even_block_minus.md`: the divided difference `Tight.D F (q + 1)` of the
ideals `TheoremB.DIdeal F (q + 1)` and `Tight.VLam F (q + 1)` is `D(y_a, y_b) = (y_a + y_b)^{q−1}`. -/
theorem D_succ_eq (S : ColSetting F) {m : ℕ} (a b : Fin m) :
    Tight.D F (S.q + 1) a b = (Tight.y F (S.q + 1) a + Tight.y F (S.q + 1) b) ^ (S.q - 1) := by
  rw [ColOne.D_eq_Dab, add_pow_eq_Dab S]

end EvenMinus

end
