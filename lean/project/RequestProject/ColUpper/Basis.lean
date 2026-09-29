module

public import RequestProject.ColUpper.Defs
public import RequestProject.ColSplit.Main

/-!
# Part (0) of the Theorem of `q_col_upper.md`: the monomial basis

For `m ≥ 1` the classes of the monomials `t^ν`, `0 ≤ ν_i ≤ m − 1`, form a `K`-basis of
`K[G] = ColSplit.GA K d m`, so `dim_K K[G] = m^d`.

The proof uses the alternative suggested in the file: `K[G]` is identified with the group algebra
of `(ℤ/m)^d` (`AddMonoidAlgebra K (Fin d → ZMod m)`), by the map `fold` sending `t_i` to the
basis element of the `i`-th unit vector. Under `fold` the class of a polynomial `Σ_e b_e X^e`
goes to `Σ_e b_e [e mod m]`, so the coordinate of `t^μ` is `Σ_{e ≡ μ (mod m)} b_e` (as in the
proof of (i)). The spanning part is `ColSplit.span_monomials_GA` of `q_col_splitting.md`.
-/

@[expose] public section

open MvPolynomial

namespace ColUpper

open ColSplit

section fold

variable (R : Type*) [CommRing R] (d m : ℕ)

/-- **Proof of (0)** in `q_col_upper.md`: the `R`-algebra map
`R[X_1, …, X_d] → R[(ℤ/m)^d]` sending `X_i` to the group element `e_i` (the `i`-th unit vector);
it sends `Σ_e b_e X^e` to `Σ_e b_e [e mod m]`. (Defined over any commutative ring `R`, so that it
can be used over `ℤ` in the proof of (i).) -/
noncomputable def foldP : MvPolynomial (Fin d) R →ₐ[R] AddMonoidAlgebra R (Fin d → ZMod m) :=
  aeval fun i => AddMonoidAlgebra.single (Pi.single i 1) 1

variable {R d m}

/-- **Proof of (0)** in `q_col_upper.md`: `fold(X^n) = [n mod m]`. -/
theorem foldP_prod_X_pow (n : Fin d → ℕ) :
    foldP R d m (∏ i, X i ^ n i) = AddMonoidAlgebra.single (fun i => (n i : ZMod m)) 1 := by
  simp only [foldP, map_prod, map_pow, aeval_X, AddMonoidAlgebra.single_pow, one_pow]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Proof of (0)** in `q_col_upper.md`: `fold(X_i^m − 1) = 0`, since `m e_i = 0` in `(ℤ/m)^d`. -/
theorem foldP_X_pow_sub_one (i : Fin d) : foldP R d m (X i ^ m - 1) = 0 := by
  simp only [foldP, map_sub, map_pow, aeval_X, AddMonoidAlgebra.single_pow, one_pow, map_one]
  rw [sub_eq_zero]
  have : m • (Pi.single i (1 : ZMod m) : Fin d → ZMod m) = 0 := by
    ext j
    simp [Pi.single_apply]
  rw [this]
  rfl

end fold

variable (K : Type*) [Field K] (d m : ℕ)

/-- **Proof of (0)** in `q_col_upper.md`: the `K`-algebra map
`K[G] → K[(ℤ/m)^d]`, `t_i ↦ e_i` (well defined as `m e_i = 0`). -/
noncomputable def foldGA : GA K d m →ₐ[K] AddMonoidAlgebra K (Fin d → ZMod m) :=
  Ideal.Quotient.liftₐ (gaIdeal K d m) (foldP K d m) (fun a ha => by
    refine (Ideal.span_le (I := RingHom.ker (foldP K d m).toRingHom)).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    exact foldP_X_pow_sub_one i)

variable {K d m}

/-- **Proof of (0)** in `q_col_upper.md`: `fold` on the class of a polynomial. -/
@[simp] theorem foldGA_mk (f : MvPolynomial (Fin d) K) :
    foldGA K d m (Ideal.Quotient.mk _ f) = foldP K d m f := rfl

/-- **(0)** in `q_col_upper.md`: the class `t^ν ∈ K[G]` of the monomial `X^ν`, for
`ν ∈ {0, …, m−1}^d`. -/
noncomputable def monoGA (ν : Fin d → Fin m) : GA K d m :=
  Ideal.Quotient.mk _ (∏ i, X i ^ (ν i : ℕ))

/-- **Proof of (0)** in `q_col_upper.md`: the exponent `ν ∈ {0, …, m−1}^d` read in `(ℤ/m)^d`. -/
def expZ (ν : Fin d → Fin m) : Fin d → ZMod m := fun i => ((ν i : ℕ) : ZMod m)

/-- **Proof of (0)** in `q_col_upper.md`: reduction `{0, …, m−1}^d → (ℤ/m)^d` is injective. -/
theorem expZ_injective : Function.Injective (expZ (d := d) (m := m)) := by
  intro ν ν' h
  funext i
  have h1 := congrFun h i
  simp only [expZ] at h1
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  rw [Nat.mod_eq_of_lt (ν i).2, Nat.mod_eq_of_lt (ν' i).2] at this
  exact Fin.ext this

/-- **Proof of (0)** in `q_col_upper.md`: for `m ≥ 1`, reduction `{0, …, m−1}^d → (ℤ/m)^d` is
surjective. -/
theorem expZ_surjective (hm : 0 < m) : Function.Surjective (expZ (d := d) (m := m)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  intro g
  refine ⟨fun i => ⟨(g i).val, ZMod.val_lt _⟩, ?_⟩
  funext i
  simp [expZ]

/-- **Proof of (0)** in `q_col_upper.md`: `fold(t^ν) = [ν]`. -/
theorem foldGA_monoGA (ν : Fin d → Fin m) :
    foldGA K d m (monoGA ν) = AddMonoidAlgebra.single (expZ ν) 1 := by
  rw [monoGA, foldGA_mk, foldP_prod_X_pow]
  rfl

/-- **Proof of (0)** in `q_col_upper.md`: for `m ≥ 1`, `fold : K[G] → K[(ℤ/m)^d]` is bijective. -/
theorem foldGA_bijective (hm : 0 < m) : Function.Bijective (foldGA K d m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : x ∈ Submodule.span K (Set.range (monoGA (K := K) (d := d) (m := m))) := by
      have := span_monomials_GA (F := K) d m hm
      rw [show (Set.range (monoGA (K := K) (d := d) (m := m))) = _ from rfl]
      exact this ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
    have hc : ∀ ν, c ν = 0 := by
      intro ν
      have := congrArg (fun f : AddMonoidAlgebra K (Fin d → ZMod m) => f (expZ ν)) hx
      simp only [map_sum, map_smul, foldGA_monoGA] at this
      rw [Finset.sum_apply' (f := fun i => c i • AddMonoidAlgebra.single (expZ i) (1 : K)),
        Finset.sum_eq_single ν] at this
      · simpa using this
      · intro b _ hb
        simp [expZ_injective.ne hb]
      · simp
    simp [hc]
  · intro y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add f g hf hg =>
      obtain ⟨a, rfl⟩ := hf
      obtain ⟨b, rfl⟩ := hg
      exact ⟨a + b, map_add _ _ _⟩
    | single g c =>
      obtain ⟨ν, rfl⟩ := expZ_surjective (d := d) hm g
      refine ⟨c • monoGA ν, ?_⟩
      rw [map_smul, foldGA_monoGA, AddMonoidAlgebra.smul_single', mul_one]

/-- **Proof of (0)** in `q_col_upper.md`: for `m ≥ 1`, the `K`-algebra isomorphism
`K[G] ≅ K[(ℤ/m)^d]`, `t_i ↦ e_i`. -/
noncomputable def foldEquiv (hm : 0 < m) : GA K d m ≃ₐ[K] AddMonoidAlgebra K (Fin d → ZMod m) :=
  AlgEquiv.ofBijective (foldGA K d m) (foldGA_bijective hm)

variable (K d m)

/-- **Theorem (0)** of `q_col_upper.md` (the monomial basis): for every field `K` and `m ≥ 1`,
the classes of the monomials `t^ν = t_1^{ν_1} ⋯ t_d^{ν_d}`, `0 ≤ ν_i ≤ m − 1`, form a `K`-basis of
`K[G]` (the basis vector of index `ν` is `monoGA ν`, see `monoBasis_apply`). -/
noncomputable def monoBasis (hm : 0 < m) : Module.Basis (Fin d → Fin m) K (GA K d m) :=
  Module.Basis.mk (v := monoGA (K := K) (d := d) (m := m))
    (by
      have h : LinearIndependent K (fun ν : Fin d → Fin m =>
          (Finsupp.single (expZ ν) (1 : K) : (Fin d → ZMod m) →₀ K)) :=
        (Finsupp.basisSingleOne.linearIndependent).comp _ expZ_injective
      have h2 : (fun ν : Fin d → Fin m =>
          (Finsupp.single (expZ ν) (1 : K) : (Fin d → ZMod m) →₀ K)) =
          (foldEquiv (K := K) hm).toLinearEquiv.toLinearMap ∘ monoGA := by
        funext ν
        simp only [Function.comp_apply]
        exact (foldGA_monoGA ν).symm
      rw [h2] at h
      exact h.of_comp)
    (span_monomials_GA (F := K) d m hm).ge

/-- **Theorem (0)** of `q_col_upper.md`: the basis vector of `monoBasis` of index `ν` is the class
of the monomial `t^ν`. -/
theorem monoBasis_apply (hm : 0 < m) (ν : Fin d → Fin m) :
    monoBasis K d m hm ν = Ideal.Quotient.mk _ (∏ i, X i ^ (ν i : ℕ)) := by
  rw [monoBasis, Module.Basis.mk_apply]
  rfl

/-- **Theorem (0)** of `q_col_upper.md`: for every field `K` and `m ≥ 1`,
`dim_K K[G] = m^d`. -/
theorem finrank_GA (hm : 0 < m) : Module.finrank K (GA K d m) = m ^ d := by
  rw [Module.finrank_eq_card_basis (monoBasis K d m hm), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

end ColUpper

end
