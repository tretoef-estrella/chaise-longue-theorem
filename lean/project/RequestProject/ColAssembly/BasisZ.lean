module

public import RequestProject.ColUpper.Integral

/-!
# The basis of `R` over `ℤ` (proof of Main Theorem′ of `q_col_assembly.md`)

* `RZ d m := ℤ[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)` is the ring `R` of the Setting of
  `q_col_assembly.md` (for `d = 2k + 1`), and `IZ m k ⊆ RZ (2k+1) m` is the ideal
  `I_ℤ = (ψ_J : J a matching)`, `ψ_J` being the image of the polynomial
  `ColUpper.psiP ℤ m J` (the same formula as in `q_col_upper.md`).
* `monoBasisZ d m hm`: for `m ≥ 1`, `R` is a free `ℤ`-module with basis the monomials `t^ν`,
  `0 ≤ ν_i < m` (the proof of (0) of `q_col_upper.md` over `ℤ`).
* `map_equivFun_IZ`: under the coordinate map `e : R ≅ ℤ^n` of this basis, `e(I_ℤ)` is the `ℤ`-span
  `L` of the rows of the integer matrix `A = ColUpper.intMatU m k` of (i) of `q_col_upper.md`.
-/

@[expose] public section

open MvPolynomial

namespace ColAssembly

open ColSplit ColSurv ColUpper

set_option synthInstance.maxHeartbeats 200000

variable (d m : ℕ)

/-- **Setting** of `q_col_assembly.md`: the ideal `(t_1^m − 1, …, t_d^m − 1)` of
`ℤ[t_1, …, t_d]`. -/
def idealZ : Ideal (MvPolynomial (Fin d) ℤ) :=
  Ideal.span (Set.range fun i : Fin d => (X i ^ m - 1 : MvPolynomial (Fin d) ℤ))

/-- **Setting** of `q_col_assembly.md`: `R := ℤ[t_1, …, t_d]/(t_1^m − 1, …, t_d^m − 1)`. -/
abbrev RZ : Type := MvPolynomial (Fin d) ℤ ⧸ idealZ d m

/-- **Setting** of `q_col_assembly.md`: `I_ℤ := (ψ_J : J a matching) ⊆ R` (with `d = 2k + 1`),
where `ψ_J` is the image in `R` of the polynomial `ψ_J^ℤ = ColUpper.psiP ℤ m J` given by the same
formula as in `q_col_upper.md`. -/
noncomputable def IZ (k : ℕ) : Ideal (RZ (2 * k + 1) m) :=
  Ideal.span (Set.range fun J : BallotBound.Matching k =>
    Ideal.Quotient.mk (idealZ (2 * k + 1) m) (psiP ℤ m J))

variable {d m}

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): the class `t^ν ∈ R` of the
monomial `X^ν`, for `ν ∈ {0, …, m−1}^d`. -/
noncomputable def monoRZ (ν : Fin d → Fin m) : RZ d m :=
  Ideal.Quotient.mk _ (∏ i, X i ^ (ν i : ℕ))

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*, as in (0) of
`q_col_upper.md`): for `m ≥ 1` the monomials `t^ν`, `0 ≤ ν_i < m`, span `R` over `ℤ`. -/
theorem span_monoRZ (hm : 0 < m) :
    Submodule.span ℤ (Set.range (monoRZ (d := d) (m := m))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hX : ∀ i : Fin d, (Ideal.Quotient.mk (idealZ d m) (X i)) ^ m = 1 := by
    intro i
    rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (idealZ d m)), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  have key : ∀ e : Fin d →₀ ℕ, Ideal.Quotient.mk (idealZ d m) (monomial e 1) ∈
      Submodule.span ℤ (Set.range (monoRZ (d := d) (m := m))) := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % m, Nat.mod_lt _ hm⟩, ?_⟩
    show Ideal.Quotient.mk (idealZ d m) (∏ i, X i ^ (e i % m)) = _
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_pow]
    conv_rhs => rw [← Nat.mod_add_div (e i) m, pow_add, pow_mul, hX, one_pow, mul_one]
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun v _ => ?_
  have : (monomial v (coeff v f) : MvPolynomial (Fin d) ℤ) = coeff v f • monomial v 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_zsmul]
  exact Submodule.smul_mem _ _ (key v)

variable (d m)

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): the ring map
`R → ℤ[(ℤ/m)^d]`, `t_i ↦ e_i` (the map `fold` of (0) of `q_col_upper.md`, over `ℤ`). -/
noncomputable def foldRZ : RZ d m →ₐ[ℤ] AddMonoidAlgebra ℤ (Fin d → ZMod m) :=
  Ideal.Quotient.liftₐ (idealZ d m) (foldP ℤ d m) (fun a ha => by
    refine (Ideal.span_le (I := RingHom.ker (foldP ℤ d m).toRingHom)).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    exact foldP_X_pow_sub_one i)

variable {d m}

/-- **Proof of Main Theorem′** in `q_col_assembly.md`: `fold` on the class of a polynomial. -/
@[simp] theorem foldRZ_mk (f : MvPolynomial (Fin d) ℤ) :
    foldRZ d m (Ideal.Quotient.mk _ f) = foldP ℤ d m f := rfl

/-- **Proof of Main Theorem′** in `q_col_assembly.md`: `fold(t^ν) = [ν]`. -/
theorem foldRZ_monoRZ (ν : Fin d → Fin m) :
    foldRZ d m (monoRZ ν) = AddMonoidAlgebra.single (expZ ν) 1 := by
  rw [monoRZ, foldRZ_mk, foldP_prod_X_pow]
  rfl

variable (d m)

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): for `m ≥ 1`, `R` is a free
`ℤ`-module with basis the monomials `t^ν`, `0 ≤ ν_i < m` (as in (0) of `q_col_upper.md`; the
same proof works over `ℤ`). -/
noncomputable def monoBasisZ (hm : 0 < m) : Module.Basis (Fin d → Fin m) ℤ (RZ d m) :=
  Module.Basis.mk (v := monoRZ (d := d) (m := m))
    (by
      have h : LinearIndependent ℤ (fun ν : Fin d → Fin m =>
          (Finsupp.single (expZ ν) (1 : ℤ) : (Fin d → ZMod m) →₀ ℤ)) :=
        (Finsupp.basisSingleOne.linearIndependent).comp _ expZ_injective
      have h2 : (fun ν : Fin d → Fin m =>
          (Finsupp.single (expZ ν) (1 : ℤ) : (Fin d → ZMod m) →₀ ℤ)) =
          (foldRZ d m).toLinearMap ∘ monoRZ := by
        funext ν
        simp only [Function.comp_apply]
        exact (foldRZ_monoRZ ν).symm
      rw [h2] at h
      exact h.of_comp)
    (span_monoRZ hm).ge

variable {d m}

/-- **Proof of Main Theorem′** in `q_col_assembly.md`: the basis vector of `monoBasisZ` of index
`ν` is `t^ν`. -/
theorem monoBasisZ_apply (hm : 0 < m) (ν : Fin d → Fin m) : monoBasisZ d m hm ν = monoRZ ν := by
  rw [monoBasisZ, Module.Basis.mk_apply]

/-- **Proof of Main Theorem′** in `q_col_assembly.md`: the coordinates of `x ∈ R` in the monomial
basis are the coefficients of `fold(x) ∈ ℤ[(ℤ/m)^d]`. -/
theorem monoBasisZ_repr (hm : 0 < m) (x : RZ d m) (ν : Fin d → Fin m) :
    (monoBasisZ d m hm).repr x ν = foldRZ d m x (expZ ν) := by
  have : (Finsupp.lapply ν).comp (monoBasisZ d m hm).repr.toLinearMap =
      (Finsupp.lapply (expZ ν)).comp (foldRZ d m).toLinearMap := by
    refine (monoBasisZ d m hm).ext fun ν' => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply]
    rw [monoBasisZ_apply]
    show _ = foldRZ d m (monoRZ ν') (expZ ν)
    rw [foldRZ_monoRZ]
    by_cases h : ν' = ν
    · subst h; simp
    · simp [h, expZ_injective.ne h]
  exact congrArg (fun φ => φ x) this

variable {k : ℕ}

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): by the construction in (i) of
`q_col_upper.md`, the coordinate vector of `t^ν ψ_J` is the row `(ν, J)` of `A`. -/
theorem equivFun_rowZ (hm : 0 < m) (ν : Fin (2 * k + 1) → Fin m) (J : BallotBound.Matching k) :
    (monoBasisZ (2 * k + 1) m hm).equivFun
        (monoRZ ν * Ideal.Quotient.mk (idealZ (2 * k + 1) m) (psiP ℤ m J)) =
      (intMatU m k).row (ν, J) := by
  funext μ
  rw [Module.Basis.equivFun_apply, monoBasisZ_repr, monoRZ, ← map_mul, foldRZ_mk]
  rfl

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): `I_ℤ` is the `ℤ`-span of the
elements `t^ν ψ_J`. -/
theorem IZ_eq_span (hm : 0 < m) :
    (IZ m k).restrictScalars ℤ =
      Submodule.span ℤ (Set.range fun x : (Fin (2 * k + 1) → Fin m) × BallotBound.Matching k =>
        monoRZ x.1 * Ideal.Quotient.mk (idealZ (2 * k + 1) m) (psiP ℤ m x.2)) := by
  have htop : Submodule.span ℤ (Set.range (monoRZ (d := 2 * k + 1) (m := m))) = ⊤ :=
    span_monoRZ hm
  have hV : IZ m k = Submodule.span (RZ (2 * k + 1) m) (Set.range fun J : BallotBound.Matching k =>
      Ideal.Quotient.mk (idealZ (2 * k + 1) m) (psiP ℤ m J)) := rfl
  rw [hV, ← Submodule.span_smul_of_span_eq_top htop]
  congr 1
  ext x
  simp only [Set.mem_smul, Set.mem_range, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
    exact ⟨(a, J), rfl⟩
  · rintro ⟨⟨a, J⟩, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨J, rfl⟩, rfl⟩

/-- **Proof of Main Theorem′** in `q_col_assembly.md` (*The basis*): `e(I_ℤ) = L`, the `ℤ`-span
of the rows of `A`, where `e : R ≅ ℤ^n` is the coordinate map of the monomial basis. -/
theorem map_equivFun_IZ (hm : 0 < m) :
    ((IZ m k).restrictScalars ℤ).map
        ((monoBasisZ (2 * k + 1) m hm).equivFun : RZ (2 * k + 1) m →ₗ[ℤ] _) =
      Submodule.span ℤ (Set.range (intMatU m k).row) := by
  rw [IZ_eq_span hm, Submodule.map_span, ← Set.range_comp]
  refine congrArg (fun s => Submodule.span ℤ (Set.range s)) (funext fun x => ?_)
  exact equivFun_rowZ hm x.1 x.2

end ColAssembly

end
