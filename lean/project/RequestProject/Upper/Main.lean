module

public import RequestProject.Upper.Count
public import RequestProject.Upper.Top
public import RequestProject.Main

/-!
# An upper bound for the ideal `V`, and equality (`q3_upper_bound.md`)

Formalization of the **Theorem (upper bound)** and the **Corollary (equality)** of
`q3_upper_bound.md`: if `char F ≠ 2`, then `dim_F V ≤ binomial(2k + 2, k + 1)`, and hence
(with `BallotBound.finrank_V_ge`) `dim_F V = binomial(2k + 2, k + 1)`.

Step (iv) of the source (top-degree forms, `dim_F C/V ≥ dim_F S/I`) is carried out degree by
degree: writing `V_d` for the image in `C` of the forms of degree `d` of the ideal
`(g_J : J ∈ 𝒥)` and `W` for the space of functions on `T^{n'}` given by elements of that ideal,
filtered by the degree `W_{<d}`, we show `dim V_d + dim W_{<d} ≤ dim W_{<d+1}` (this is the
injectivity of "taking top-degree forms", i.e. `mem_squaresIdeal_of_eval_eq`), and sum over `d`.
By step (iii), `W` consists of functions vanishing off `Σ`, so `dim W ≤ |Σ|`.
-/

@[expose] public section

open MvPolynomial Finset Module

namespace BallotBound

variable {F : Type*} [Field F] {k : ℕ}

/-- The image of `g_J` in `C` is `D_J` (**Proof of the Theorem** of `q3_upper_bound.md`:
`g_J` is "the same product as `D_J`, before passing to `C`"). -/
theorem mk_g (J : Matching k) : Ideal.Quotient.mk (squaresIdeal F k) (g J) = D J := by
  rw [g, D, map_prod]
  refine prod_congr rfl fun a _ => ?_
  rw [map_sub]
  have : ∀ x, Ideal.Quotient.mk (squaresIdeal F k) (yP F k x) = y F k x := by
    intro x; refine Fin.cases ?_ (fun j => ?_) x <;> simp [yP, y]
  rw [this, this]

/-- The image of the ideal `(g_J : J ∈ 𝒥) ⊆ S` in `C` is `V` (step (iv) of
`q3_upper_bound.md`: `C/V = S/I'`). -/
theorem map_G : (G F k).map (Ideal.Quotient.mk (squaresIdeal F k)) = V F k := by
  rw [G, Ideal.map_span, V, ← Set.range_comp]
  congr 2
  funext J
  exact mk_g J

/-- Each `g_J` is homogeneous (**Proof of the Theorem** of `q3_upper_bound.md`). -/
theorem g_isHomogeneous (J : Matching k) : ∃ m, (g (F := F) J).IsHomogeneous m := by
  refine ⟨_, IsHomogeneous.prod _ _ (fun _ => 1) fun a ha => ?_⟩
  simp only [mem_filter, mem_univ, true_and] at ha
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr ha.1
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr ha.2.1
  rw [← hj, ← hi]
  simp only [yP, Fin.cases_succ]
  exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

/-- The ideal `(g_J : J ∈ 𝒥)` is homogeneous: the homogeneous components of its elements
belong to it (since each `g_J` is homogeneous; used in step (iv) of `q3_upper_bound.md`). -/
theorem homogeneousComponent_mem_G {p : MvPolynomial (Fin (2 * k + 1)) F} (hp : p ∈ G F k)
    (d : ℕ) : homogeneousComponent d p ∈ G F k := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := Fin (2 * k + 1)) (R := F)
  have hG : (G F k).IsHomogeneous (homogeneousSubmodule (Fin (2 * k + 1)) F) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨J, rfl⟩
    obtain ⟨m, hm⟩ := g_isHomogeneous (F := F) J
    exact ⟨m, hm⟩
  have := hG d hp
  rwa [← decomposition.decompose'_apply]

/-- A form of degree `d > n'` lies in `(y_1^2, …, y_{n'}^2)` (so `C` lives in degrees `≤ n'`;
step (v) of `q3_upper_bound.md`). -/
theorem mem_squaresIdeal_of_isHomogeneous {d : ℕ} {p : MvPolynomial (Fin (2 * k + 1)) F}
    (hp : p.IsHomogeneous d) (hd : 2 * k + 1 < d) : p ∈ squaresIdeal F k := by
  rw [mem_squaresIdeal_iff]
  intro m hm
  have hmd := hp (mem_support_iff.mp hm)
  by_contra hc
  push_neg at hc
  have : (Finsupp.weight 1) m ≤ 2 * k + 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    calc ∑ i, m i • (1 : Fin (2 * k + 1) → ℕ) i ≤ ∑ _i : Fin (2 * k + 1), 1 :=
          sum_le_sum fun i _ => by simpa using Nat.lt_succ_iff.mp (hc i)
      _ = 2 * k + 1 := by simp
  omega

variable (F k) in
/-- Evaluation on `T^{n'}`: the `F`-linear map `S → F^{T^{n'}}` of step (iii) of
`q3_upper_bound.md` (points of `T^{n'}` encoded by subsets, see `BallotBound.pt`). -/
noncomputable def Ev : MvPolynomial (Fin (2 * k + 1)) F →ₗ[F] (Finset (Fin (2 * k + 1)) → F) where
  toFun p A := eval (pt F k A) p
  map_add' p q := by ext A; simp
  map_smul' c p := by ext A; simp

variable (F k) in
/-- The space `F^{T^{n'}}` of functions on `T^{n'}` is finite dimensional (a shortcut for
instance search; step (iii) of `q3_upper_bound.md`). -/
instance instFiniteFun : Module.Finite F (Finset (Fin (2 * k + 1)) → F) :=
  Module.Finite.pi

/-- Step (iii) of `q3_upper_bound.md`: every element of `(g_J : J ∈ 𝒥)` vanishes on
`T^{n'} ∖ Σ`. -/
theorem Ev_eq_zero_of_mem_G {p : MvPolynomial (Fin (2 * k + 1)) F} (hp : p ∈ G F k)
    {A : Finset (Fin (2 * k + 1))} (hA : A ∉ supp F k) : Ev F k p A = 0 := by
  classical
  have hle : G F k ≤ RingHom.ker (eval (pt F k A)) := by
    rw [G, Ideal.span_le]
    rintro _ ⟨J, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    by_contra h
    exact hA (by rw [supp, mem_filter]; exact ⟨mem_univ _, J, h⟩)
  exact hle hp

/-- Step (iii) of `q3_upper_bound.md`: the space of functions on `T^{n'}` given by elements of
`(g_J : J ∈ 𝒥)` has dimension at most `|Σ|` (they vanish on `T^{n'} ∖ Σ`). -/
theorem finrank_map_Ev_G_le :
    finrank F (((G F k).restrictScalars F).map (Ev F k)) ≤ (supp F k).card := by
  classical
  set W := ((G F k).restrictScalars F).map (Ev F k)
  let r : W →ₗ[F] (supp F k → F) :=
    (LinearMap.funLeft F F (fun A : supp F k => A.1)).comp W.subtype
  have hr : Function.Injective r := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨f, hf⟩ hk
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hf
    ext A
    by_cases hA : A ∈ supp F k
    · exact congrFun hk ⟨A, hA⟩
    · exact Ev_eq_zero_of_mem_G hp hA
  have := LinearMap.finrank_le_finrank_of_injective hr
  simpa using this

variable (F k) in
/-- Polynomials all of whose monomials have degree `< d` (the degree filtration used for the
top-degree forms of step (iv) of `q3_upper_bound.md`). -/
noncomputable def low (d : ℕ) : Submodule F (MvPolynomial (Fin (2 * k + 1)) F) :=
  restrictSupport F {m | m.degree < d}

variable (F k) in
/-- `W_{<d}`: functions on `T^{n'}` given by elements of `(g_J : J ∈ 𝒥)` which are also given
by polynomials of degree `< d` (step (iv) of `q3_upper_bound.md`). -/
noncomputable def Wlt (d : ℕ) : Submodule F (Finset (Fin (2 * k + 1)) → F) :=
  ((G F k).restrictScalars F).map (Ev F k) ⊓ (low F k d).map (Ev F k)

variable (F k) in
/-- `V_d ⊆ C`: the image of the forms of degree `d` lying in `(g_J : J ∈ 𝒥)`
(step (iv) of `q3_upper_bound.md`). -/
noncomputable def Vdeg (d : ℕ) : Submodule F (Alg F k) :=
  ((G F k).restrictScalars F ⊓ homogeneousSubmodule (Fin (2 * k + 1)) F d).map
    (Ideal.Quotient.mkₐ F (squaresIdeal F k)).toLinearMap

/-- Linear algebra: if `ker f ≤ ker g` then `dim range g ≤ dim range f`. -/
theorem finrank_range_le_of_ker_le {K M N P : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [FiniteDimensional K N]
    (f : M →ₗ[K] N) (g : M →ₗ[K] P) (h : LinearMap.ker f ≤ LinearMap.ker g) :
    finrank K (LinearMap.range g) ≤ finrank K (LinearMap.range f) := by
  rw [← f.quotKerEquivRange.finrank_eq, ← g.quotKerEquivRange.finrank_eq]
  haveI : FiniteDimensional K (M ⧸ LinearMap.ker f) :=
    LinearEquiv.finiteDimensional f.quotKerEquivRange.symm
  have := LinearMap.finrank_range_le (Submodule.factor h)
  rwa [LinearMap.range_eq_top.mpr (Submodule.factor_surjective h), finrank_top] at this

/-- Step (iv) of `q3_upper_bound.md`, in degree `d`: `dim V_d + dim W_{<d} ≤ dim W_{<d+1}`.
This is where top-degree forms enter, through `mem_squaresIdeal_of_eval_eq`. -/
theorem finrank_Vdeg_add_le (hF : ringChar F ≠ 2) (d : ℕ) :
    finrank F (Vdeg F k d) + finrank F (Wlt F k d) ≤ finrank F (Wlt F k (d + 1)) := by
  classical
  set E' := (low F k d).map (Ev F k) with hE'
  set Q := (G F k).restrictScalars F ⊓ homogeneousSubmodule (Fin (2 * k + 1)) F d with hQ
  let Φ := E'.mkQ ∘ₗ Ev F k ∘ₗ Q.subtype
  let Ψ := (Ideal.Quotient.mkₐ F (squaresIdeal F k)).toLinearMap ∘ₗ Q.subtype
  have hΨ : LinearMap.range Ψ = Vdeg F k d := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  -- taking top-degree forms is injective: this is `mem_squaresIdeal_of_eval_eq`
  have hker : LinearMap.ker Φ ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hxG, hxd⟩ hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp only [Φ, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨q, hq, hqx⟩ := Submodule.mem_map.mp hx
    simp only [Ψ, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    refine mem_squaresIdeal_of_eval_eq hF (q := q) hxd ?_ ?_
    · intro m hm
      exact hq hm
    · intro A
      exact (congrFun hqx A).symm
  have hlow : low F k d ≤ low F k (d + 1) :=
    restrictSupport_mono _ fun m (h : m.degree < d) => (Nat.lt_succ_of_lt h : m.degree < d + 1)
  have hW : Wlt F k d ≤ Wlt F k (d + 1) := inf_le_inf_left _ (Submodule.map_mono hlow)
  have hrange : LinearMap.range Φ ≤ (Wlt F k (d + 1)).map E'.mkQ := by
    rintro _ ⟨⟨x, hxG, hxd⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨Ev F k x, ⟨Submodule.mem_map_of_mem hxG,
      Submodule.mem_map_of_mem ?_⟩, rfl⟩
    intro m hm
    have := hxd (mem_support_iff.mp hm)
    show m.degree < d + 1
    rw [Finsupp.degree_eq_weight_one]
    exact Nat.lt_succ_of_le this.le
  have hrank : finrank F ((Wlt F k (d + 1)).map E'.mkQ) + finrank F (Wlt F k d) =
      finrank F (Wlt F k (d + 1)) := by
    have := LinearMap.finrank_range_add_finrank_ker (E'.mkQ.domRestrict (Wlt F k (d + 1)))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at this
    have heq : (E').comap (Wlt F k (d + 1)).subtype =
        (Wlt F k d).comap (Wlt F k (d + 1)).subtype := by
      ext ⟨x, hx⟩
      simp only [Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    rw [heq, (Submodule.comapSubtypeEquivOfLe hW).finrank_eq] at this
    exact this
  have h1 : finrank F (Vdeg F k d) ≤ finrank F (LinearMap.range Φ) := by
    have := finrank_range_le_of_ker_le Φ Ψ hker
    rwa [hΨ] at this
  have h2 := Submodule.finrank_mono hrange
  omega

/-- Step (iv) of `q3_upper_bound.md`, summed over degrees: `∑_{d < N} dim V_d ≤ dim W_{<N}`. -/
theorem sum_finrank_Vdeg_le (hF : ringChar F ≠ 2) (N : ℕ) :
    ∑ d ∈ range N, finrank F (Vdeg F k d) ≤ finrank F (Wlt F k N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have := finrank_Vdeg_add_le (k := k) hF N
    omega

/-- `V` is spanned by its homogeneous pieces `V_d`, `d ≤ n'` (step (iv) of `q3_upper_bound.md`). -/
theorem V_le_iSup_Vdeg :
    (V F k).restrictScalars F ≤ ⨆ d ∈ range (2 * k + 2), Vdeg F k d := by
  intro v hv
  rw [Submodule.restrictScalars_mem, ← map_G,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  rw [← sum_homogeneousComponent p, map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  by_cases hd : d < 2 * k + 2
  · refine (le_biSup (f := Vdeg F k) (mem_range.2 hd)) ?_
    exact Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ F (squaresIdeal F k)).toLinearMap)
      (⟨homogeneousComponent_mem_G hp d, homogeneousComponent_isHomogeneous d p⟩ :
        homogeneousComponent d p ∈ (G F k).restrictScalars F ⊓
          homogeneousSubmodule (Fin (2 * k + 1)) F d)
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_squaresIdeal_of_isHomogeneous (homogeneousComponent_isHomogeneous d p) (by omega))]
    exact Submodule.zero_mem _

/-- Linear algebra: the dimension of a finite supremum of subspaces is at most the sum of their
dimensions. -/
theorem finrank_biSup_le {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (s : Finset ℕ) (W : ℕ → Submodule K M) :
    finrank K ↥(⨆ d ∈ s, W d) ≤ ∑ d ∈ s, finrank K (W d) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)

/-- **Theorem (upper bound)** of `q3_upper_bound.md`: if `char F ≠ 2`, then for every `k ≥ 0`
the ideal `V ⊆ C` generated by all `D_J` satisfies `dim_F V ≤ binomial(2k + 2, k + 1)`.
(Step (v): `dim V ≤ ∑_d dim V_d ≤ dim W ≤ |Σ| ≤ binomial(2k+2, k+1)`.) -/
theorem finrank_V_le (F : Type*) [Field F] (hF : ringChar F ≠ 2) (k : ℕ) :
    Module.finrank F ((V F k).restrictScalars F) ≤ (2 * k + 2).choose (k + 1) := by
  calc Module.finrank F ((V F k).restrictScalars F)
      ≤ finrank F ↥(⨆ d ∈ range (2 * k + 2), Vdeg F k d) :=
        Submodule.finrank_mono V_le_iSup_Vdeg
    _ ≤ ∑ d ∈ range (2 * k + 2), finrank F (Vdeg F k d) := finrank_biSup_le _ _
    _ ≤ finrank F (Wlt F k (2 * k + 2)) := sum_finrank_Vdeg_le hF _
    _ ≤ finrank F (((G F k).restrictScalars F).map (Ev F k)) := by
        haveI := FiniteDimensional.finiteDimensional_submodule
          (((G F k).restrictScalars F).map (Ev F k))
        exact Submodule.finrank_mono inf_le_left
    _ ≤ (supp F k).card := finrank_map_Ev_G_le
    _ ≤ (2 * k + 2).choose (k + 1) := card_supp_le

/-- **Corollary (equality)** of `q3_upper_bound.md`: if `char F ≠ 2`, then
`dim_F V = binomial(2k + 2, k + 1)` for every `k ≥ 0`, combining the **Theorem (upper bound)**
(`finrank_V_le`) with the lower bound `finrank_V_ge` of `q3_ballot_lower_bound.md`. -/
theorem finrank_V_eq (F : Type*) [Field F] (hF : ringChar F ≠ 2) (k : ℕ) :
    Module.finrank F ((V F k).restrictScalars F) = (2 * k + 2).choose (k + 1) :=
  le_antisymm (finrank_V_le F hF k) (finrank_V_ge F k)

end BallotBound

end
