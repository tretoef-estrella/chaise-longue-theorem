module

public import Mathlib

/-!
# Definitions for the peeling lemma (`q_peeling_lemma.md`)

This file formalizes the **Setting** section of `q_peeling_lemma.md`: the rings `C_m`, the
identification `C_m = C_{m−1}[y_1]/(y_1^{q−1})`, the coefficients `[y_1^j] f`, the degree
`deg_{y_1} f`, the spaces `V_{≤j}` and `W_j(V)`, and (for the counting part) the fibres `F(M')`
and the sets `Z_{>i}`.

Encoding conventions (used throughout):
* the variables `y_1, …, y_m` of `C_m` are `X 0, …, X (m-1)` (indexed by `Fin m`); in particular
  `y_1 = X 0`, and the variables `y_2, …, y_m` of `C_{m−1}` are `X 0, …, X (m-2)` of `C_{m-1}`
  (the variable `y_{i+1}` of `C_m` corresponds to the variable `X i` of `C_{m−1}`);
* the ring `C_{m−1}[y_1]/(y_1^{q−1})` is `AdjoinRoot (X ^ (q - 1))` over `C_{m−1}`, i.e. the
  quotient of the polynomial ring `C_{m−1}[X]` by the principal ideal `(X^{q−1})`, with `y_1` the
  root `AdjoinRoot.root`;
* all objects depending on the identification take a proof `hm : 1 ≤ m`.
-/

@[expose] public section

open MvPolynomial Polynomial

namespace Peel

set_option synthInstance.maxHeartbeats 200000

variable (F : Type*) [Field F] (q : ℕ)

/-- The ideal `(y_1^{q−1}, …, y_m^{q−1})` of `F[y_1, …, y_m]` from the **Setting** of
`q_peeling_lemma.md` (variables `y_i = X (i - 1)`, indexed by `Fin m`).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def powIdeal (m : ℕ) : Ideal (MvPolynomial (Fin m) F) :=
  Ideal.span (Set.range fun i : Fin m => (MvPolynomial.X i ^ (q - 1) : MvPolynomial (Fin m) F))

/-- The ring `C_m := F[y_1, …, y_m] / (y_1^{q−1}, …, y_m^{q−1})` of the **Setting** of
`q_peeling_lemma.md`.  For `m = 0` this is `F[] / (0) ≅ F`, matching the convention `C_0 = F`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
abbrev C (m : ℕ) : Type _ := MvPolynomial (Fin m) F ⧸ powIdeal F q m

/-- `C_m` as a module over itself (a shortcut for instance search, used to regard ideals of
`C_m` as `F`-subspaces); this is the usual structure `Semiring.toModule`.  Part of the
**Setting** of `q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable instance instModuleCSelf (m : ℕ) : Module (C F q m) (C F q m) := Semiring.toModule

/-- `C_m` is a commutative ring (a shortcut for instance search).  Part of the **Setting** of
`q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable instance instCommRingC (m : ℕ) : CommRing (C F q m) := Ideal.Quotient.commRing _

/-- `C_m` is an `F`-algebra (a shortcut for instance search).  Part of the **Setting** of
`q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable instance instAlgebraC (m : ℕ) : Algebra F (C F q m) := Ideal.Quotient.algebra _

/-- The ring `C_{m−1}[y_1]/(y_1^{q−1})` of the **Setting** of `q_peeling_lemma.md`, written with
base ring `R = C_{m−1}`: it is `AdjoinRoot (X ^ (q - 1))`, the quotient of `R[X]` by `(X^{q−1})`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
abbrev Peeled (R : Type*) [CommRing R] : Type _ := AdjoinRoot (Polynomial.X ^ (q - 1) : R[X])

/-- The polynomial `y_1^{q−1}` defining `C_{m−1}[y_1]/(y_1^{q−1})` is monic (so the unique
expansion `f = Σ_{j=0}^{q−2} f_j y_1^j` of the **Setting** of `q_peeling_lemma.md` exists).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem monic_X_pow_q (R : Type*) [CommRing R] : (Polynomial.X ^ (q - 1) : R[X]).Monic :=
  Polynomial.monic_X_pow _

/-- The ring map `C_{m−1} → C_m` sending the variable `y_{i+1}` of `C_{m−1}` (encoded `X i`) to
`y_{i+2}` (encoded `X (i+1)`) of `C_m`; used to build the identification of the **Setting** of
`q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def incl (n : ℕ) : C F q n →+* C F q (n + 1) :=
  Ideal.Quotient.lift (powIdeal F q n)
    ((Ideal.Quotient.mk (powIdeal F q (n + 1))).comp (rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom)
    (by
      intro a ha
      refine (Ideal.span_le.2 ?_ : powIdeal F q n ≤ RingHom.ker _) ha
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, map_pow, rename_X]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i.succ, rfl⟩))

/-- The forward half of the identification `C_m ≅ C_{m−1}[y_1]/(y_1^{q−1})` (with `m = n + 1`)
from the **Setting** of `q_peeling_lemma.md`: `y_1 ↦ y_1` (the root) and `y_{i+2} ↦ y_{i+2} ∈
C_{m−1}`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def peelFwd (n : ℕ) : C F q (n + 1) →ₐ[F] Peeled q (C F q n) :=
  Ideal.Quotient.liftₐ (powIdeal F q (n + 1))
    (MvPolynomial.aeval (Fin.cases (AdjoinRoot.root _)
      (fun i => AdjoinRoot.of _ (Ideal.Quotient.mk (powIdeal F q n) (MvPolynomial.X i)))))
    (by
      intro a ha
      refine (Ideal.span_le.2 ?_ : powIdeal F q (n + 1) ≤ RingHom.ker _) ha
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [map_pow, MvPolynomial.aeval_X, Fin.cases_zero]
        rw [← AdjoinRoot.mk_X, ← map_pow]
        exact AdjoinRoot.mk_self
      · have h0 : Ideal.Quotient.mk (powIdeal F q n) (MvPolynomial.X i ^ (q - 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
        rw [map_pow, MvPolynomial.aeval_X, Fin.cases_succ, ← map_pow, ← map_pow, h0, map_zero])

/-- The backward half of the identification `C_m ≅ C_{m−1}[y_1]/(y_1^{q−1})` (with `m = n + 1`)
from the **Setting** of `q_peeling_lemma.md`, as a ring map.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def peelBwd (n : ℕ) : Peeled q (C F q n) →+* C F q (n + 1) :=
  AdjoinRoot.lift (incl F q n) (Ideal.Quotient.mk _ (MvPolynomial.X 0)) (by
    simp only [eval₂_X_pow, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩))

/-- The backward half of the identification of the **Setting** of `q_peeling_lemma.md`, as an
`F`-algebra map.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def peelBwdₐ (n : ℕ) : Peeled q (C F q n) →ₐ[F] C F q (n + 1) :=
  { peelBwd F q n with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply F (C F q n), AdjoinRoot.algebraMap_eq, peelBwd,
        AdjoinRoot.lift_of, ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, incl,
        Ideal.Quotient.lift_mk]
      simp }

/-- The identification `C_m = C_{m−1}[y_1]/(y_1^{q−1})` of the **Setting** of
`q_peeling_lemma.md`, for `m = n + 1`, as an `F`-algebra isomorphism.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def peelEquiv' (n : ℕ) : C F q (n + 1) ≃ₐ[F] Peeled q (C F q n) :=
  AlgEquiv.ofAlgHom (peelFwd F q n) (peelBwdₐ F q n)
    (by
      apply AlgHom.coe_ringHom_injective
      apply AdjoinRoot.ringHom_ext
      · apply Ideal.Quotient.ringHom_ext
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [peelBwdₐ, peelBwd, incl, peelFwd]
          rw [IsScalarTower.algebraMap_apply F (C F q n), AdjoinRoot.algebraMap_eq,
            ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
        · intro i
          simp [peelBwdₐ, peelBwd, incl, peelFwd]
      · simp [peelBwdₐ, peelBwd, peelFwd])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [peelBwdₐ, peelBwd, peelFwd]
      · simp [peelBwdₐ, peelBwd, incl, peelFwd])

/-- The identification `C_m = C_{m−1}[y_1]/(y_1^{q−1})` of the **Setting** of
`q_peeling_lemma.md`, for every `m ≥ 1`, as an `F`-algebra isomorphism.  It sends `y_1 = X 0` to
the root `y_1` and the variable `y_{i+1} = X i` (`i ≥ 1`) of `C_m` to the constant `X (i-1)`
(the variable `y_{i+1}`) of `C_{m−1}`.  (For `m = n + 1`, `C_{m-1}` is definitionally `C_n`.)
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def peelEquiv : (m : ℕ) → 1 ≤ m → (C F q m ≃ₐ[F] Peeled q (C F q (m - 1)))
  | n + 1, _ => peelEquiv' F q n

/-- The `F`-linear map `C_{m−1}[y_1]/(y_1^{q−1}) → C_{m−1}[y_1]` (written for an arbitrary
`F`-algebra `R` in place of `C_{m−1}`) sending an element to its unique representative
`Σ_{j=0}^{q−2} f_j y_1^j` of degree `< q − 1`; this is the unique expansion of the **Setting** of
`q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def expandGen (R : Type*) [CommRing R] [Algebra F R] : Peeled q R →ₗ[F] R[X] :=
  (AdjoinRoot.modByMonicHom (monic_X_pow_q q R)).restrictScalars F

/-- The `F`-linear coefficient map `p ↦ [y_1^j] p` on `R[y_1]` (for an `F`-algebra `R`), used for
the coefficients `[y_1^j] f` of the **Setting** of `q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def lcoeffGen (R : Type*) [CommRing R] [Algebra F R] (j : ℕ) : R[X] →ₗ[F] R :=
  (Polynomial.lcoeff R j).restrictScalars F

/-- The `F`-subspace `{p ∈ R[y_1] : deg p ≤ j}` (for an `F`-algebra `R`), used to define
`V_{≤j}` in the **Setting** of `q_peeling_lemma.md`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def degLE (R : Type*) [CommRing R] [Algebra F R] (j : ℕ) : Submodule F R[X] :=
  (Polynomial.degreeLE R j).restrictScalars F

variable {F q}

/-- The unique representative `Σ_{j=0}^{q−2} f_j y_1^j ∈ C_{m−1}[y_1]` (degree `< q − 1`) of
`f ∈ C_m`, from the **Setting** of `q_peeling_lemma.md`: the remainder modulo `y_1^{q−1}` of any
lift of `f` under the identification `peelEquiv`.  It is `F`-linear.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def expand {m : ℕ} (hm : 1 ≤ m) : C F q m →ₗ[F] (C F q (m - 1))[X] :=
  (expandGen F q (C F q (m - 1))).comp (peelEquiv F q m hm).toLinearMap

/-- The coefficient `[y_1^j] f := f_j ∈ C_{m−1}` of the **Setting** of `q_peeling_lemma.md`,
where `f = Σ_{j=0}^{q−2} f_j y_1^j` is the unique expansion; it is `F`-linear in `f`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def coeffY1 {m : ℕ} (hm : 1 ≤ m) (j : ℕ) : C F q m →ₗ[F] C F q (m - 1) :=
  (lcoeffGen F (C F q (m - 1)) j).comp (expand hm)

/-- The degree `deg_{y_1} f := max {j : f_j ≠ 0}` of the **Setting** of `q_peeling_lemma.md`, with
`deg_{y_1} 0 = −∞` (encoded as `⊥ : WithBot ℕ`).  It is the degree of the expansion
`Σ_j f_j y_1^j`.
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def degY1 {m : ℕ} (hm : 1 ≤ m) (f : C F q m) : WithBot ℕ :=
  (expand hm f).degree

/-- The space `V_{≤j} := {f ∈ V : deg_{y_1} f ≤ j}` of the **Setting** of `q_peeling_lemma.md`,
as an `F`-subspace of `C_m` (it is closed under addition and `F`-scaling).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def Vle {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) : Submodule F (C F q m) :=
  V.restrictScalars F ⊓ (degLE F (C F q (m - 1)) j).comap (expand hm)

/-- The space `W_j(V) := {[y_1^j] f : f ∈ V_{≤j}} ⊆ C_{m−1}` of the **Setting** of
`q_peeling_lemma.md`, i.e. the image of `V_{≤j}` under `f ↦ [y_1^j] f`, as an `F`-subspace of
`C_{m−1}` (its underlying set is exactly the displayed set).
Used in parts (i), (ii) and (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
noncomputable def W {m : ℕ} (hm : 1 ≤ m) (V : Ideal (C F q m)) (j : ℕ) :
    Submodule F (C F q (m - 1)) :=
  (Vle hm V j).map (coeffY1 hm j)

/-- The tuple `(t, M') = (t, t_2, …, t_m) ∈ T^m` for `t ∈ T` and a tail `M' ∈ T^{m−1}`, from the
**Setting** of `q_peeling_lemma.md` (for `m ≥ 1`): coordinate `0` (i.e. `t_1`) is `t`, and
coordinate `i ≥ 1` is `M' (i - 1)`.
Used in part (iv) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
def consTuple {T : Type*} {m : ℕ} (t : T) (M' : Fin (m - 1) → T) : Fin m → T :=
  fun i => if h : (i : ℕ) = 0 then t else M' ⟨i - 1, by omega⟩

/-- The fibre `F(M') := {t ∈ T : (t, M') ∈ Z}` of the **Setting** of `q_peeling_lemma.md`.
Used in part (iv) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
def fiber {T : Type*} [Fintype T] [DecidableEq T] {m : ℕ} (Z : Finset (Fin m → T))
    (M' : Fin (m - 1) → T) : Finset T :=
  Finset.univ.filter fun t => consTuple t M' ∈ Z

/-- The set `Z_{>i} := {M' ∈ T^{m−1} : |F(M')| > i}` of the **Setting** of
`q_peeling_lemma.md`.
Used in part (iv) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
def Zgt {T : Type*} [Fintype T] [DecidableEq T] {m : ℕ} (Z : Finset (Fin m → T)) (i : ℕ) :
    Finset (Fin (m - 1) → T) :=
  Finset.univ.filter fun M' => i < (fiber Z M').card

end Peel

end
