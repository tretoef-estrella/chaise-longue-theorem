module

public import RequestProject.ColSplit.Basic

/-!
# Lemma 6.1 (i), (ii), (iii) of `q_col_splitting.md`

* `ColSplit.ColSetting.piMap` is the product map `π = (π_c)_{c ∈ μ^d} : F[G] → Π_c R_c`.
* `lemma61_i` : `π` is bijective, and `piEquiv` is the resulting `F`-algebra isomorphism.
* `lemma61_ii` : `dim_F I' = Σ_c dim_F π_c(I')` for every ideal `I'` of `F[G]`.
* `lemma61_iii` : `π_c(⟨E⟩) = ⟨π_c(E)⟩`.

The proof of (i) follows the file: `dim_F F[G] ≤ m^d` (the monomials `t^a`, `0 ≤ a_i ≤ m − 1`,
span `F[G]`), `dim_F R_c ≥ q^d` (the products `Π_i (t_i − c_i)^{b_i}`, `0 ≤ b_i ≤ q − 1`, are
linearly independent in `R_c`, by the change of variables `s_i = t_i − c_i`), `π` is surjective by
the Chinese remainder theorem for the pairwise comaximal ideals `J_c`, and a surjective linear map
between spaces of the same finite dimension `m^d = r^d q^d` is bijective.
-/

@[expose] public section

open MvPolynomial

namespace ColSplit

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-! ### Dimension of `F[G]` -/

/-- **Proof of Lemma 6.1 (i)**, *Dimensions*, of `q_col_splitting.md`: for `m ≥ 1`, the classes
of the monomials `t^a`, `0 ≤ a_i ≤ m − 1`, span `F[G]`. -/
theorem span_monomials_GA (d m : ℕ) (hm : 0 < m) :
    Submodule.span F (Set.range fun a : Fin d → Fin m =>
      (Ideal.Quotient.mk (gaIdeal F d m) (∏ i, X i ^ (a i : ℕ)))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hX : ∀ i : Fin d, (Ideal.Quotient.mk (gaIdeal F d m) (X i)) ^ m = 1 := by
    intro i
    rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (gaIdeal F d m)), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  have key : ∀ e : Fin d →₀ ℕ, Ideal.Quotient.mk (gaIdeal F d m) (monomial e 1) ∈
      Submodule.span F (Set.range fun a : Fin d → Fin m =>
      (Ideal.Quotient.mk (gaIdeal F d m) (∏ i, X i ^ (a i : ℕ)))) := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % m, Nat.mod_lt _ hm⟩, ?_⟩
    show Ideal.Quotient.mk (gaIdeal F d m) (∏ i, X i ^ (e i % m)) = _
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_pow]
    conv_rhs => rw [← Nat.mod_add_div (e i) m, pow_add, pow_mul, hX, one_pow, mul_one]
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun v _ => ?_
  have : (monomial v (coeff v f) : MvPolynomial (Fin d) F) = coeff v f • monomial v 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, show Ideal.Quotient.mk (gaIdeal F d m) (coeff v f • monomial v 1) =
    coeff v f • Ideal.Quotient.mk (gaIdeal F d m) (monomial v 1) from
    map_smul (Ideal.Quotient.mkₐ F (gaIdeal F d m)) _ _]
  exact Submodule.smul_mem _ _ (key v)

/-- **Proof of Lemma 6.1 (i)**, *Dimensions*, of `q_col_splitting.md`: for `m ≥ 1`, `F[G]` is
finite-dimensional. -/
theorem finite_GA (d m : ℕ) (hm : 0 < m) : Module.Finite F (GA F d m) := by
  have h := span_monomials_GA (F := F) d m hm
  rw [← Fintype.range_linearCombination, LinearMap.range_eq_top] at h
  exact Module.Finite.of_surjective _ h

/-- **Proof of Lemma 6.1 (i)**, *Dimensions*, of `q_col_splitting.md`: for `m ≥ 1`,
`dim_F F[G] ≤ m^d`. -/
theorem finrank_GA_le (d m : ℕ) (hm : 0 < m) : Module.finrank F (GA F d m) ≤ m ^ d := by
  haveI := finite_GA (F := F) d m hm
  have h := finrank_range_le_card (R := F) (fun a : Fin d → Fin m =>
      (Ideal.Quotient.mk (gaIdeal F d m) (∏ i, X i ^ (a i : ℕ))))
  rw [Set.finrank, span_monomials_GA d m hm, finrank_top] at h
  simpa using h

/-! ### Dimension of `R_c` -/

/-- **Proof of Lemma 6.1 (i)**, *Dimensions*, of `q_col_splitting.md`: the products
`Π_i (t_i − c_i)^{b_i}`, `0 ≤ b_i ≤ q − 1`, are linearly independent in `R_c`. -/
theorem linearIndependent_Rc {d : ℕ} (q : ℕ) (c : Fin d → F) :
    LinearIndependent F (fun b : Fin d → Fin q =>
      (Ideal.Quotient.mk (Jc q c) (∏ i, (X i - C (c i)) ^ (b i : ℕ)))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set σ : MvPolynomial (Fin d) F →ₐ[F] MvPolynomial (Fin d) F := aeval fun i => X i - C (c i)
  set τ : MvPolynomial (Fin d) F →ₐ[F] MvPolynomial (Fin d) F := aeval fun i => X i + C (c i)
  have hτσ : ∀ f, τ (σ f) = f := by
    intro f
    rw [← AlgHom.comp_apply]
    conv_rhs => rw [← AlgHom.id_apply (R := F) f]
    congr 1
    apply MvPolynomial.algHom_ext
    intro i
    simp [σ, τ]
  let e : (Fin d → Fin q) → (Fin d →₀ ℕ) := fun b => Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ)
  have he : Function.Injective e := by
    intro b b' h
    funext i
    have := congrArg (fun f : Fin d →₀ ℕ => f i) h
    exact Fin.ext (by simpa [e] using this)
  set P : MvPolynomial (Fin d) F := ∑ b, monomial (e b) (g b) with hP
  have hσP : σ P = ∑ b, g b • ∏ i, (X i - C (c i)) ^ (b i : ℕ) := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [monomial_eq, map_mul, Finsupp.prod_fintype _ _ (by simp), map_prod]
    simp [σ, e, Algebra.smul_def]
  have hmem : σ P ∈ Jc q c := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hσP, map_sum]
    rw [← hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact map_smul (Ideal.Quotient.mkₐ F (Jc q c)) _ _
  have hPmem : P ∈ Ideal.span ((fun s => monomial s (1 : F)) ''
      Set.range fun i : Fin d => Finsupp.single i q) := by
    have := Ideal.mem_map_of_mem τ hmem
    rw [hτσ, Jc, Ideal.map_span, ← Set.range_comp] at this
    convert this using 3
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [τ, X_pow_eq_monomial]
  rw [mem_ideal_span_monomial_image] at hPmem
  intro b
  by_contra hb
  have hcoeff : coeff (e b) P = g b := by
    rw [hP, coeff_sum, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      rw [coeff_monomial, if_neg (fun h => hb' (he h))]
    · simp
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hPmem (e b) (by rw [mem_support_iff, hcoeff]; exact hb)
  have := hi i
  simp [e] at this
  omega

/-- **Proof of Lemma 6.1 (i)**, *Dimensions*, of `q_col_splitting.md`: if `R_c` is
finite-dimensional, then `dim_F R_c ≥ q^d`. -/
theorem le_finrank_Rc {d : ℕ} (q : ℕ) (c : Fin d → F) [Module.Finite F (Rc F q c)] :
    q ^ d ≤ Module.finrank F (Rc F q c) := by
  simpa using (linearIndependent_Rc (F := F) q c).fintype_card_le_finrank

/-! ### Comaximality -/

/-- **Proof of Lemma 6.1 (i)**, *Surjectivity*, of `q_col_splitting.md`: for `c ≠ c'`, the
ideals `J_c` and `J_{c'}` are comaximal. -/
theorem isCoprime_Jc {d : ℕ} (q : ℕ) {c c' : Fin d → F} (h : c ≠ c') :
    IsCoprime (Jc q c) (Jc q c') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hp : IsCoprime ((Polynomial.X - Polynomial.C (c i)) ^ q)
      ((Polynomial.X - Polynomial.C (c' i)) ^ q) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hi).isUnit).pow
  obtain ⟨a, b, hab⟩ :=
    hp.map (Polynomial.aeval (R := F) (X i : MvPolynomial (Fin d) F)).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, MvPolynomial.algebraMap_eq] at hab
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)))

/-! ### Ideals of a product -/

/-- **Proof of Lemma 6.1 (ii)** of `q_col_splitting.md`, in abstract form: if
`π = (π_c)_c : A → Π_c B_c` is bijective and each `π_c` is surjective, then for every ideal `I'`
of `A`, `dim_F I' = Σ_c dim_F π_c(I')`. (For `y ∈ π(I')`, each `e_c y ∈ π(I')`, where `e_c` is
the idempotent with component `1` at `c` and `0` elsewhere.) -/
theorem finrank_ideal_eq_sum {A : Type*} [CommRing A] [Algebra F A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ i, CommRing (B i)]
    [∀ i, Algebra F (B i)] [∀ i, Module.Finite F (B i)]
    (φ : ∀ i, A →ₐ[F] B i) (hsurj : ∀ i, Function.Surjective (φ i))
    (hbij : Function.Bijective (Pi.algHom F B φ)) (I : Ideal A) :
    Module.finrank F (I.restrictScalars F) =
      ∑ i, Module.finrank F ((I.map (φ i)).restrictScalars F) := by
  let J : ∀ i, Submodule F (B i) := fun i => (I.map (φ i)).restrictScalars F
  have hg : ∀ i x, ((φ i).toLinearMap ∘ₗ (I.restrictScalars F).subtype) x ∈ J i := fun i x =>
    Ideal.mem_map_of_mem (φ i) x.2
  let Φ := LinearMap.pi fun i => LinearMap.codRestrict (J i) _ (hg i)
  have hΦc : ∀ x i, (Φ x i : B i) = φ i x := fun x i => rfl
  let e := AlgEquiv.ofBijective _ hbij
  have he : ∀ x i, e x i = φ i x := fun x i => rfl
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hbij.1
      funext i
      change φ i x = φ i y
      rw [← hΦc, ← hΦc, hxy]
    · intro y
      have hy : ∀ i, ∃ x ∈ I, φ i x = (y i : B i) := fun i =>
        (Ideal.mem_map_iff_of_surjective _ (hsurj i)).1 (y i).2
      choose x hxI hx using hy
      let ε : ι → A := fun i => e.symm (Pi.single i 1)
      refine ⟨⟨∑ i, ε i * x i, Submodule.sum_mem _ fun i _ => I.mul_mem_left _ (hxI i)⟩, ?_⟩
      funext j
      apply Subtype.ext
      rw [hΦc, ← he]
      change e (∑ i, ε i * x i) j = _
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same, one_mul,
          he, hx]
      · intro i _ hi
        rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne hi.symm,
          zero_mul]
      · simp
  rw [(LinearEquiv.ofBijective Φ hΦ).finrank_eq, Module.finrank_pi_fintype]

namespace ColSetting

variable (S : ColSetting F)

/-- **Lemma 6.1 (i)** of `q_col_splitting.md`: the product map
`π := (π_c)_{c ∈ μ^d} : F[G] → Π_{c ∈ μ^d} R_c`. -/
noncomputable def piMap (d : ℕ) :
    GA F d S.m →ₐ[F] ((c : Fin d → S.μ) → Rc F S.q (fun j => (c j : F))) :=
  Pi.algHom F _ fun c => S.piC c

/-- **Setting** of `q_col_splitting.md`: `m ≥ 1`. -/
theorem m_pos : 0 < S.m :=
  Nat.mul_pos (pow_pos S.hp.pos _) S.one_le_r

instance instFiniteGA (d : ℕ) : Module.Finite F (GA F d S.m) := finite_GA d S.m S.m_pos

instance instFiniteRc {d : ℕ} (c : Fin d → S.μ) :
    Module.Finite F (Rc F S.q (fun j => (c j : F))) :=
  Module.Finite.of_surjective (S.piC c).toLinearMap (S.lemma61_0_surjective c)

/-- **Proof of Lemma 6.1 (i)**, *Surjectivity*, of `q_col_splitting.md`: `π` is surjective
(Chinese remainder theorem). -/
theorem piMap_surjective (d : ℕ) : Function.Surjective (S.piMap d) := by
  intro y
  obtain ⟨f, hf⟩ := Ideal.pi_quotient_surjective
    (I := fun c : Fin d → S.μ => Jc S.q (fun j => (c j : F))) (fun c c' h => isCoprime_Jc _
      (fun h' => h (funext fun j => Subtype.ext (congrFun h' j)))) y
  exact ⟨Ideal.Quotient.mk _ f, funext hf⟩

/-- **Lemma 6.1 (i)** of `q_col_splitting.md`: the product map `π : F[G] → Π_{c ∈ μ^d} R_c` is
bijective (hence an isomorphism of `F`-algebras, see `piEquiv`). -/
theorem lemma61_i (d : ℕ) : Function.Bijective (S.piMap d) := by
  have hsurj := S.piMap_surjective d
  refine ⟨?_, hsurj⟩
  have hB : Module.finrank F ((c : Fin d → S.μ) → Rc F S.q (fun j => (c j : F))) ≤
      Module.finrank F (GA F d S.m) := by
    have h := LinearMap.finrank_range_le (S.piMap d).toLinearMap
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
  have hA := finrank_GA_le (F := F) d S.m S.m_pos
  have hC : S.m ^ d ≤ Module.finrank F ((c : Fin d → S.μ) → Rc F S.q (fun j => (c j : F))) := by
    rw [Module.finrank_pi_fintype]
    calc S.m ^ d = ∑ _c : Fin d → S.μ, S.q ^ d := by
          simp [ColSetting.m, mul_pow, S.card_μ, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun c _ => le_finrank_Rc _ _
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)
    (f := (S.piMap d).toLinearMap)).2 hsurj

/-- **Lemma 6.1 (i)** of `q_col_splitting.md`: the product map
`π : F[G] ≃ₐ[F] Π_{c ∈ μ^d} R_c` as an isomorphism of `F`-algebras. -/
noncomputable def piEquiv (d : ℕ) :
    GA F d S.m ≃ₐ[F] ((c : Fin d → S.μ) → Rc F S.q (fun j => (c j : F))) :=
  AlgEquiv.ofBijective (S.piMap d) (S.lemma61_i d)

/-- **Lemma 6.1 (i)** of `q_col_splitting.md`: the isomorphism `piEquiv` is the product map `π`,
i.e. its `c`-component is `π_c`. -/
theorem piEquiv_apply (d : ℕ) (x : GA F d S.m) (c : Fin d → S.μ) :
    S.piEquiv d x c = S.piC c x := rfl

/-- **Lemma 6.1 (ii)** of `q_col_splitting.md`: for every ideal `I'` of `F[G]`,
`dim_F I' = Σ_{c ∈ μ^d} dim_F π_c(I')`. -/
theorem lemma61_ii (d : ℕ) (I' : Ideal (GA F d S.m)) :
    Module.finrank F (I'.restrictScalars F) =
      ∑ c : Fin d → S.μ, Module.finrank F ((I'.map (S.piC c)).restrictScalars F) := by
  classical
  exact finrank_ideal_eq_sum (fun c => S.piC c) S.lemma61_0_surjective (S.lemma61_i d) I'

/-- **Lemma 6.1 (iii)** of `q_col_splitting.md`: if `I'` is generated by `E ⊆ F[G]`, then
`π_c(I')` is the ideal of `R_c` generated by `π_c(E)`. -/
theorem lemma61_iii {d : ℕ} (c : Fin d → S.μ) (E : Set (GA F d S.m)) :
    (Ideal.span E).map (S.piC c) = Ideal.span (S.piC c '' E) :=
  Ideal.map_span _ _

end ColSetting

end ColSplit
