module

public import RequestProject.Induction.Main
public import RequestProject.Degeneration.Main
public import RequestProject.Lifts.Options

/-!
# Setting of `q_support.md`

This file formalizes the **Setting** section of `q_support.md`.

* `F` is a field, `q ≥ 3` is odd, `h = (q − 1)/2`, and `T ⊆ F` is a `Finset F` with `|T| = q − 1`
  and `Π_{u∈T}(y − u) = y^{q−1} − 1`.  The consequences `q − 1 ≠ 0` in `F`, `char F ≠ 2`,
  `−1 ∈ T` and "`u ↦ −u` is a fixed-point-free involution of `T`" are proved here, and
  `Support.fibreSetting` is the resulting `Fibres.FibreSetting` of `q_P1_fibres.md` on (the type
  of elements of) `T`, with `u ↦ −u`.  Its `ZLam` is `Z_Λ = {M ∈ T^m : λ(M) ∈ Λ}`.
* The tight-pattern products of `q_P3_identities.md` (`Tight.TightPattern.prod`, elements of
  `C_m = Peel.C F q m`) are lifted to polynomials of `F[y_1, …, y_m] = MvPolynomial (Fin m) F`:
  `DP` (`D(y_a, y_b)`), `DeltaP` (`Δ(B)`), `pairDP` and `prodP` (the product `G`).  Their images in
  `C_m` are the original elements, and they are homogeneous.
-/

@[expose] public section

open MvPolynomial

namespace Support

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-! ### Consequences of the hypotheses on `T` (Setting of `q_support.md`) -/

/-- **Setting** of `q_support.md`: every `u ∈ T` is a root of `y^{q−1} − 1`, i.e. `u^{q−1} = 1`. -/
theorem pow_eq_one {q : ℕ} {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {u : F} (hu : u ∈ T) : u ^ (q - 1) = 1 :=
  Degeneration.pow_eq_one_of_mem hprod hu

/-- **Setting** of `q_support.md`: conversely every root of `y^{q−1} − 1` lies in `T`. -/
theorem mem_of_pow_eq_one {q : ℕ} {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {v : F} (hv : v ^ (q - 1) = 1) : v ∈ T := by
  have h := congrArg (Polynomial.eval v) hprod
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_one, hv, sub_self] at h
  obtain ⟨u, hu, huv⟩ := Finset.prod_eq_zero_iff.1 h
  rw [sub_eq_zero] at huv
  exact huv ▸ hu

/-- **Setting** of `q_support.md`: `q − 1 ≠ 0` in `F` (the roots of `y^{q−1} − 1` are simple). -/
theorem natCast_sub_one_ne_zero {q : ℕ} {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1) :
    ((q - 1 : ℕ) : F) ≠ 0 := by
  have hsep : (∏ u ∈ T, (Polynomial.X - Polynomial.C (id u))).Separable :=
    Polynomial.separable_prod_X_sub_C_iff'.2 (fun x _ y _ h => h)
  simp only [id, hprod] at hsep
  exact Polynomial.X_pow_sub_one_separable_iff.1 hsep

/-- **Setting** of `q_support.md`: `char F ≠ 2`, i.e. `2 ≠ 0` in `F` (as `q − 1` is even). -/
theorem two_ne_zero' {q : ℕ} (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1) :
    (2 : F) ≠ 0 := by
  intro h2
  apply natCast_sub_one_ne_zero hprod
  obtain ⟨k, rfl⟩ := hodd
  rw [show 2 * k + 1 - 1 = 2 * k by omega]
  push_cast
  rw [h2, zero_mul]

/-- **Setting** of `q_support.md`: `T` is stable under `u ↦ −u` (`q − 1` is even). -/
theorem neg_mem {q : ℕ} (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {u : F} (hu : u ∈ T) : -u ∈ T := by
  apply mem_of_pow_eq_one hprod
  have h1 := pow_eq_one hprod hu
  obtain ⟨k, rfl⟩ := hodd
  rw [show 2 * k + 1 - 1 = 2 * k by omega] at h1 ⊢
  rw [pow_mul, neg_sq, ← pow_mul, h1]

/-- **Setting** of `q_support.md`: `−1 ∈ T`. -/
theorem neg_one_mem {q : ℕ} (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1) :
    (-1 : F) ∈ T :=
  neg_mem hodd hprod (mem_of_pow_eq_one hprod (one_pow _))

/-- **Setting** of `q_support.md`: the elements of `T` are nonzero. -/
theorem ne_zero_of_mem {q : ℕ} (hq : 3 ≤ q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {u : F} (hu : u ∈ T) : u ≠ 0 := by
  rintro rfl
  have := pow_eq_one hprod hu
  rw [zero_pow (by omega)] at this
  exact zero_ne_one this

/-- **Setting** of `q_support.md`: `u ↦ −u` has no fixed point on `T` (`−u = u` would give
`2u = 0`). -/
theorem neg_ne_self {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) {T : Finset F}
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1)
    {u : F} (hu : u ∈ T) : -u ≠ u := by
  intro h
  have h2 : (2 : F) * u = 0 := by
    have : u + u = 0 := by nth_rewrite 1 [← h]; exact neg_add_cancel u
    rw [two_mul]; exact this
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact two_ne_zero' hodd hprod h2
  · exact ne_zero_of_mem hq hprod hu h2

/-- **Setting** of `q_support.md`: `T` with the involution `u ↦ −u` satisfies the Setting of
`q_P1_fibres.md` with `h = (q − 1)/2` (a fixed-point-free involution of a set of `2h = q − 1`
elements, `h ≥ 1`).  Its residue partition `resPart M` is `λ(M)` and its `ZLam m Λ` is
`Z_Λ = {M ∈ T^m : λ(M) ∈ Λ}`. -/
noncomputable def fibreSetting {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (T : Finset F)
    (hT : T.card = q - 1)
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1) :
    Fibres.FibreSetting T ((q - 1) / 2) where
  neg u := ⟨-(u : F), neg_mem hodd hprod u.2⟩
  neg_neg u := by simp
  neg_ne u := fun h => neg_ne_self hq hodd hprod u.2 (congrArg Subtype.val h)
  one_le := by omega
  card_eq := by
    rw [Fintype.card_coe, hT]; obtain ⟨k, rfl⟩ := hodd; omega

/-- **Setting** of `q_support.md`: the involution of `fibreSetting` is `u ↦ −u`. -/
@[simp] theorem fibreSetting_neg {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) (T : Finset F)
    (hT : T.card = q - 1)
    (hprod : ∏ u ∈ T, (Polynomial.X - Polynomial.C u) = Polynomial.X ^ (q - 1) - 1) (u : T) :
    ((fibreSetting hq hodd T hT hprod).neg u : F) = -(u : F) := rfl

/-! ### The tight-pattern products as polynomials (Setting of `q_support.md`) -/

variable (F) (q : ℕ)

/-- **Setting** of `q_support.md`: `D(y_a, y_b) = Σ_{i=0}^{q−2} (−1)^i y_a^i y_b^{q−2−i}` as a
polynomial of `F[y_1, …, y_m]` (homogeneous of degree `q − 2`). -/
noncomputable def DP {m : ℕ} (a b : Fin m) : MvPolynomial (Fin m) F :=
  ∑ i ∈ Finset.range (q - 1), (-1) ^ i * X a ^ i * X b ^ (q - 2 - i)

/-- **Setting** of `q_support.md`: `Δ(B) = Π_{c<c'} (y_{b_{c'}} − y_{b_c})` as a polynomial of
`F[y_1, …, y_m]` (homogeneous of degree `|B|(|B| − 1)/2`). -/
noncomputable def DeltaP {m : ℕ} (B : Finset (Fin m)) : MvPolynomial (Fin m) F := vand X B

/-- **Setting** of `q_support.md`: the factor `D(y_a, y_b)` of a pair `{a < b}` of a tight
pattern, as a polynomial (the lift of `Tight.pairD`). -/
noncomputable def pairDP {m : ℕ} (e : Finset (Fin m)) : MvPolynomial (Fin m) F :=
  if h : e.Nonempty then DP F q (e.min' h) (e.max' h) else 1

/-- **Setting** of `q_support.md`: the product `G = Π_{{a<b}∈P} D(y_a, y_b) · Π_c Δ(B_c)` of a
tight pattern, as a polynomial of `F[y_1, …, y_m]` (the lift of `Tight.TightPattern.prod`). -/
noncomputable def prodP {m : ℕ} {lam : Partition} {I : Finset (Fin m)} (Tp : TightPattern lam I) :
    MvPolynomial (Fin m) F :=
  (∏ e ∈ Tp.pairs, pairDP F q e) * ∏ c ∈ Finset.Icc 1 (lam.row 1), DeltaP F (Tp.blocks c)

/-- **Setting** of `q_support.md`: the image of `prodP` in `C_m` is the product of the tight
pattern of `q_P3_identities.md`. -/
theorem mk_prodP {m : ℕ} {lam : Partition} {I : Finset (Fin m)} (Tp : TightPattern lam I) :
    Ideal.Quotient.mk (Peel.powIdeal F q m) (prodP F q Tp) = Tp.prod F q := by
  have hvand : ∀ B : Finset (Fin m),
      Ideal.Quotient.mk (Peel.powIdeal F q m) (DeltaP F B) = Delta F q B := by
    intro B
    simp only [DeltaP, Delta, vand, map_prod, map_sub]
    rfl
  simp only [prodP, TightPattern.prod, map_mul, map_prod, hvand]
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  unfold pairDP pairD
  split_ifs
  · simp only [DP, D, map_sum, map_mul, map_pow, map_neg, map_one]
    rfl
  · exact map_one _

/-- **Setting** of `q_support.md`: `prodP` is homogeneous (`D(y_a, y_b)` of degree `q − 2`,
`Δ(B)` of degree `|B|(|B| − 1)/2`, and products of homogeneous polynomials are homogeneous). -/
theorem prodP_isHomogeneous {m : ℕ} {lam : Partition} {I : Finset (Fin m)}
    (Tp : TightPattern lam I) : ∃ n, (prodP F q Tp).IsHomogeneous n := by
  have hmul : ∀ {f g : MvPolynomial (Fin m) F}, (∃ n, f.IsHomogeneous n) →
      (∃ n, g.IsHomogeneous n) → ∃ n, (f * g).IsHomogeneous n := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨a + b, ha.mul hb⟩
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin m) F),
      (∀ i ∈ s, ∃ n, (f i).IsHomogeneous n) → ∃ n, (∏ i ∈ s, f i).IsHomogeneous n := by
    intro ι s f hf
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simpa using isHomogeneous_one (Fin m) F⟩
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hmul (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hD : ∀ a b : Fin m, ∃ n, (DP F q a b).IsHomogeneous n := by
    intro a b
    refine ⟨q - 2, ?_⟩
    refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    have h1 : ((-1 : MvPolynomial (Fin m) F) ^ i).IsHomogeneous 0 := by
      rw [← map_one C, ← map_neg C, ← map_pow C]; exact isHomogeneous_C _ _
    have := (h1.mul (isHomogeneous_X_pow a i)).mul (isHomogeneous_X_pow b (q - 2 - i))
    rwa [show 0 + i + (q - 2 - i) = q - 2 by omega] at this
  refine hmul (hprod _ _ fun e _ => ?_) (hprod _ _ fun c _ => ?_)
  · unfold pairDP
    split_ifs
    · exact hD _ _
    · exact ⟨0, isHomogeneous_one _ _⟩
  · exact hprod _ _ fun c _ => hprod _ _ fun c' _ =>
      ⟨1, (isHomogeneous_X F c').sub (isHomogeneous_X F c)⟩

end Support

end
