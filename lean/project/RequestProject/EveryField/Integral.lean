module

public import RequestProject.Support.Defs
public import RequestProject.EveryField.Rank

/-!
# Part (i) of the Theorem of `q_every_field.md`: the integral spanning set

Formalization of **part (i)** of the Theorem of `q_every_field.md`.

* The tight-pattern products of `q_P3_identities.md` are written over an arbitrary commutative
  ring `R` (`DPR`, `DeltaPR`, `pairDPR`, `prodPR`), by the same formulas as `Support.DP`, …,
  `Support.prodP` of `q_support.md` (which are the case of a field).  Over `R = ℤ` this is the
  integer polynomial `G_ℤ`, and its image in `F[y]` is the polynomial of `F` (`map_prodPR`).
* `B_m = {0, …, q−2}^m` is `Box q m` (`Fin m → Fin (q - 1)`), and the exponent vector of the box
  monomial `y^a` is `boxExp a`.  The box monomials `y^a ∈ C_m(F)` are `boxMono`, and
  `boxToC : F^{B_m} → C_m(F)` sends a coordinate vector `w` to `Σ_a w_a y^a`.
* For a polynomial `p`, reducing modulo the monomial ideal `(y_i^{q−1})` kills exactly the
  monomials outside the box, so the coordinates of the reduction of `p` are the coefficients of
  `p` at the box monomials.  Hence `v_{a,G} ∈ ℤ^{B_m}` is `intVec q a G_ℤ`,
  `b ↦ [y^b] (y^a · G_ℤ)`, and the integer matrix `A` (rows `v_{a,G}`) is `intMat q m Λ`, whose
  rows are indexed by `B_m × 𝒢`, `𝒢 = GZ q m Λ` the (finite) set of the polynomials `G_ℤ`.
-/

@[expose] public section

open MvPolynomial

namespace EveryField

open ChainLemma Tight

set_option synthInstance.maxHeartbeats 200000

/-! ### The tight-pattern products over a commutative ring -/

section Ring

variable (R : Type*) [CommRing R] (q : ℕ)

/-- **Part (i)** of `q_every_field.md`: `D(y_a, y_b) = Σ_{i=0}^{q−2} (−1)^i y_a^i y_b^{q−2−i}` as a
polynomial with coefficients in a commutative ring `R` (for `R = ℤ`: integer coefficients). -/
noncomputable def DPR {m : ℕ} (a b : Fin m) : MvPolynomial (Fin m) R :=
  ∑ i ∈ Finset.range (q - 1), (-1) ^ i * X a ^ i * X b ^ (q - 2 - i)

/-- **Part (i)** of `q_every_field.md`: the Vandermonde `Δ(B) = Π_{c<c'} (y_{b_{c'}} − y_{b_c})`
as a polynomial with coefficients in a commutative ring `R`. -/
noncomputable def DeltaPR {m : ℕ} (B : Finset (Fin m)) : MvPolynomial (Fin m) R := vand X B

/-- **Part (i)** of `q_every_field.md`: the factor `D(y_a, y_b)` of a pair `{a < b}` of a tight
pattern, as a polynomial over `R`. -/
noncomputable def pairDPR {m : ℕ} (e : Finset (Fin m)) : MvPolynomial (Fin m) R :=
  if h : e.Nonempty then DPR R q (e.min' h) (e.max' h) else 1

/-- **Part (i)** of `q_every_field.md`: the product `G = Π_{{a<b}∈P} D(y_a, y_b) · Π_c Δ(B_c)` of
a tight pattern as a polynomial over a commutative ring `R`; for `R = ℤ` this is `G_ℤ`, which does
not depend on any field. -/
noncomputable def prodPR {m : ℕ} {lam : Partition} {I : Finset (Fin m)} (Tp : TightPattern lam I) :
    MvPolynomial (Fin m) R :=
  (∏ e ∈ Tp.pairs, pairDPR R q e) * ∏ c ∈ Finset.Icc 1 (lam.row 1), DeltaPR R (Tp.blocks c)

variable {R}

/-- **Part (i)** of `q_every_field.md`: the formula for `G` is the same over every ring: a ring
map `R → S` sends the polynomial `G` over `R` to the polynomial `G` over `S` (in particular
`ℤ[y] → F[y]` sends `G_ℤ` to `G`). -/
theorem map_prodPR {S : Type*} [CommRing S] (f : R →+* S) {m : ℕ} {lam : Partition}
    {I : Finset (Fin m)} (Tp : TightPattern lam I) :
    MvPolynomial.map f (prodPR R q Tp) = prodPR S q Tp := by
  simp only [prodPR, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun e _ => ?_
    unfold pairDPR
    split_ifs
    · simp [DPR]
    · simp
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [DeltaPR, vand]

end Ring

variable (F : Type*) [Field F] (q : ℕ)

/-- **Part (i)** of `q_every_field.md` (first claim): every tight-pattern product `G ∈ C_m(F)` is
the image of the integer polynomial `G_ℤ ∈ ℤ[y_1, …, y_m]` (under `ℤ[y] → F[y] → C_m(F)`). -/
theorem mk_map_prodPR_int {m : ℕ} {lam : Partition} {I : Finset (Fin m)}
    (Tp : TightPattern lam I) :
    Ideal.Quotient.mk (Peel.powIdeal F q m)
      (MvPolynomial.map (Int.castRingHom F) (prodPR ℤ q Tp)) = Tp.prod F q := by
  rw [map_prodPR]
  exact Support.mk_prodP F q Tp

/-! ### Box monomials -/

/-- **Setting** of `q_every_field.md`: the index set `B_m = {0, …, q−2}^m` of the box monomials. -/
abbrev Box (q m : ℕ) : Type := Fin m → Fin (q - 1)

/-- **Setting** of `q_every_field.md`: the exponent vector of the box monomial `y^a`, `a ∈ B_m`. -/
noncomputable def boxExp {q m : ℕ} (a : Box q m) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)

/-- **Setting** of `q_every_field.md`: the `i`-th exponent of the box monomial `y^a` is `a_i`. -/
theorem boxExp_apply {q m : ℕ} (a : Box q m) (i : Fin m) : boxExp a i = a i := rfl

/-- **Setting** of `q_every_field.md`: distinct `a ∈ B_m` give distinct box monomials `y^a`. -/
theorem boxExp_injective {q m : ℕ} : Function.Injective (boxExp (q := q) (m := m)) := by
  intro a b h
  funext i
  exact Fin.ext (by simpa [boxExp_apply] using congrArg (· i) h)

/-- **Setting** of `q_every_field.md`: the box monomial `y^a ∈ C_m(F)`, `a ∈ B_m`. -/
noncomputable def boxMono {m : ℕ} (a : Box q m) : Peel.C F q m :=
  Ideal.Quotient.mk _ (monomial (boxExp a) 1)

/-- **Setting** and **part (i)** of `q_every_field.md`: the `F`-linear map `F^{B_m} → C_m(F)`,
`w ↦ Σ_{a ∈ B_m} w_a y^a` (coordinates in the box-monomial basis). -/
noncomputable def boxToC (m : ℕ) : (Box q m → F) →ₗ[F] Peel.C F q m :=
  Fintype.linearCombination F (boxMono F q)

variable {F q}

/-- **Proof of part (i)** of `q_every_field.md`: the class of a polynomial `p` in `C_m(F)` is
`Σ_{b ∈ B_m} [y^b] p · y^b` — reduction modulo the monomial ideal `(y_i^{q−1})` kills the
monomials outside the box and keeps the others. -/
theorem mk_eq_boxToC {m : ℕ} (p : MvPolynomial (Fin m) F) :
    Ideal.Quotient.mk (Peel.powIdeal F q m) p = boxToC F q m (fun b => p.coeff (boxExp b)) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    by_cases hd : ∀ i, d i < q - 1
    · let b0 : Box q m := fun i => ⟨d i, hd i⟩
      have hb0 : boxExp b0 = d := by ext i; rfl
      rw [boxToC, Fintype.linearCombination_apply, Finset.sum_eq_single b0]
      · rw [hb0, coeff_monomial, if_pos rfl, boxMono, hb0, ← Ideal.Quotient.mkₐ_eq_mk F,
          ← map_smul, smul_monomial, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [coeff_monomial, if_neg, zero_smul]
        intro h
        exact hb (boxExp_injective (h.symm ▸ hb0.symm) |>.symm ▸ rfl)
      · simp
    · push_neg at hd
      obtain ⟨i, hi⟩ := hd
      have hle : Finsupp.single i (q - 1) ≤ d := by
        rw [Finsupp.single_le_iff]; exact hi
      have hrhs : (fun b : Box q m => (monomial d c).coeff (boxExp b)) = 0 := by
        funext b
        rw [coeff_monomial, if_neg, Pi.zero_apply]
        intro h
        have := congrArg (· i) h
        simp only [boxExp_apply] at this
        have := (b i).2
        omega
      rw [hrhs, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      have : monomial d c = monomial (d - Finsupp.single i (q - 1)) c * X i ^ (q - 1) := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  | add p p' hp hp' =>
    rw [map_add, hp, hp', ← map_add]
    rfl

/-- **Setting** of `q_every_field.md`: the box monomials span `C_m(F)`. -/
theorem boxToC_surjective (m : ℕ) : Function.Surjective (boxToC F q m) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_, (mk_eq_boxToC p).symm⟩

/-- **Setting** of `q_every_field.md`: the box monomials `y^a`, `a ∈ B_m`, form an `F`-basis of
`C_m(F)` (they span, and `dim_F C_m = (q − 1)^m = |B_m|`). -/
theorem boxToC_bijective (hq : 2 ≤ q) (m : ℕ) : Function.Bijective (boxToC F q m) := by
  haveI : Module.Finite F (Peel.C F q m) := Module.Finite.of_surjective _ (boxToC_surjective m)
  refine ⟨?_, boxToC_surjective m⟩
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact boxToC_surjective m
  · rw [Degeneration.finrank_C hq, Module.finrank_fintype_fun_eq_card, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]

/-! ### The integer vectors `v_{a,G}` and the matrix `A` -/

variable (q)

/-- **Part (i)** of `q_every_field.md`: the integer vector `v_{a,G} ∈ ℤ^{B_m}`, the coefficients of
`y^a · G_ℤ` reduced modulo `(y_i^{q−1})`, i.e. `b ↦ [y^b](y^a · G_ℤ)` for `b ∈ B_m`. -/
noncomputable def intVec {m : ℕ} (a : Box q m) (G : MvPolynomial (Fin m) ℤ) : Box q m → ℤ :=
  fun b => (monomial (boxExp a) 1 * G).coeff (boxExp b)

/-- **Part (i)** of `q_every_field.md`: the set `𝒢` of the integer polynomials `G_ℤ` for `G` a
tight-pattern product (on the indices `1, …, m`) of an element of `Λ`. -/
def GZ (m : ℕ) (Λ : Set Partition) : Set (MvPolynomial (Fin m) ℤ) :=
  {G | ∃ lam ∈ Λ, ∃ Tp : TightPattern lam (Finset.univ : Finset (Fin m)), prodPR ℤ q Tp = G}

/-- **Part (i)** of `q_every_field.md`: there are finitely many polynomials `G_ℤ` (each is a
product of `D`'s over a set of pairs and of `Δ`'s over a set of subsets of `{1, …, m}`). -/
theorem GZ_finite (m : ℕ) (Λ : Set Partition) : (GZ q m Λ).Finite := by
  classical
  let Φ : Finset (Finset (Fin m)) × Finset (Finset (Fin m)) → MvPolynomial (Fin m) ℤ :=
    fun PB => (∏ e ∈ PB.1, pairDPR ℤ q e) * ∏ B ∈ PB.2, DeltaPR ℤ B
  refine (Set.finite_range Φ).subset ?_
  rintro _ ⟨lam, _, Tp, rfl⟩
  let s := (Finset.Icc 1 (lam.row 1)).filter fun c => (Tp.blocks c).Nonempty
  refine ⟨(Tp.pairs, s.image Tp.blocks), ?_⟩
  simp only [Φ, prodPR]
  congr 1
  rw [Finset.prod_image, Finset.prod_filter_of_ne]
  · intro c _ hc
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact hc (by simp [hne, DeltaPR, vand])
  · intro c hc c' hc' hcc'
    simp only [s, Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
    by_contra hne
    have hd := Tp.blocks_disjoint (Finset.mem_coe.2 hc.1) (Finset.mem_coe.2 hc'.1) hne
    rw [Function.onFun, ← hcc', disjoint_self, Finset.bot_eq_empty] at hd
    exact Finset.not_nonempty_empty (hd ▸ hc.2)

/-- **Part (i)** of `q_every_field.md`: the index set `𝒢` of the polynomials `G_ℤ` is finite. -/
instance (m : ℕ) (Λ : Set Partition) : Finite (GZ q m Λ) := (GZ_finite q m Λ).to_subtype

/-- **Part (i)** of `q_every_field.md`: the integer matrix `A` with rows `v_{a,G}`, for `a ∈ B_m`
and `G_ℤ ∈ 𝒢` (finitely many rows); its columns are indexed by `B_m`. -/
noncomputable def intMat (m : ℕ) (Λ : Set Partition) : Matrix (Box q m × GZ q m Λ) (Box q m) ℤ :=
  fun x b => intVec q x.1 x.2 b

variable {q}

/-- **Proof of part (i)** of `q_every_field.md`: the vector of `C_m(F)` with coordinates the image
of `v_{a,G}` is `y^a · G`, the class of `y^a · G_ℤ` (read over `F`). -/
theorem boxToC_intVec {m : ℕ} (a : Box q m) (G : MvPolynomial (Fin m) ℤ) :
    boxToC F q m (fun b => (intVec q a G b : F)) =
      boxMono F q a * Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom F) G) := by
  have hmono : (monomial (boxExp a) (1 : F)) =
      MvPolynomial.map (Int.castRingHom F) (monomial (boxExp a) 1) := by simp
  rw [boxMono, ← map_mul, hmono, ← map_mul, mk_eq_boxToC]
  congr 1
  funext b
  rw [coeff_map, intVec]
  rfl

/-- **Part (i)** of the Theorem of `q_every_field.md` (spanning set): as an `F`-subspace,
`V_Λ(F)` is spanned by the images over `F` of the finitely many integer vectors `v_{a,G}`
(`a ∈ B_m`, `G` a tight-pattern product of an element of `Λ`), read in the box-monomial basis. -/
theorem VLamAll_eq_span_intVec (m : ℕ) (Λ : Set Partition) :
    (VLamAll F q m Λ).restrictScalars F =
      Submodule.span F (Set.range fun x : Box q m × GZ q m Λ =>
        boxToC F q m (fun b => (intVec q x.1 x.2 b : F))) := by
  have htop : Submodule.span F (Set.range (boxMono F q (m := m))) = ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact boxToC_surjective m
  set GF : Set (Peel.C F q m) :=
    {g | ∃ lam ∈ Λ, ∃ Tp : TightPattern lam (Finset.univ : Finset (Fin m)), Tp.prod F q = g}
  have hV : VLamAll F q m Λ = Submodule.span (Peel.C F q m) GF := rfl
  rw [hV, ← Submodule.span_smul_of_span_eq_top htop]
  congr 1
  ext x
  simp only [Set.mem_smul, Set.mem_range, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨lam, hlam, Tp, rfl⟩, rfl⟩
    refine ⟨(a, ⟨prodPR ℤ q Tp, lam, hlam, Tp, rfl⟩), ?_⟩
    simp only [boxToC_intVec, mk_map_prodPR_int]
  · rintro ⟨⟨a, G, lam, hlam, Tp, hG⟩, rfl⟩
    refine ⟨_, ⟨a, rfl⟩, _, ⟨lam, hlam, Tp, rfl⟩, ?_⟩
    simp only [boxToC_intVec, ← hG, mk_map_prodPR_int]

/-- **Part (i)** of the Theorem of `q_every_field.md` (conclusion):
`dim_F V_Λ(F) = rank_F(A)`, where `A` is the integer matrix with rows `v_{a,G}` and `rank_F(A)` is
the rank of its image over `F` (`q ≥ 2`, so that the box monomials are a basis of `C_m(F)`). -/
theorem finrank_VLamAll_eq_rankOver (hq : 2 ≤ q) (m : ℕ) (Λ : Set Partition) :
    Module.finrank F ((VLamAll F q m Λ).restrictScalars F) = rankOver F (intMat q m Λ) := by
  let e : (Box q m → F) ≃ₗ[F] Peel.C F q m :=
    LinearEquiv.ofBijective (boxToC F q m) (boxToC_bijective hq m)
  have hrows : Set.range (fun x : Box q m × GZ q m Λ =>
      boxToC F q m (fun b => (intVec q x.1 x.2 b : F))) =
      (e : (Box q m → F) →ₗ[F] Peel.C F q m) ''
        Set.range ((intMat q m Λ).map (Int.castRingHom F)).row := by
    rw [← Set.range_comp]
    rfl
  rw [VLamAll_eq_span_intVec, hrows, Submodule.span_image, LinearEquiv.finrank_map_eq, rankOver,
    Matrix.rank_eq_finrank_span_row]

end EveryField

end
