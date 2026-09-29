module

public import RequestProject.ColUpper.Basis
public import RequestProject.EveryField.Rank

/-!
# Part (i) of the Theorem of `q_col_upper.md`: an integer matrix

* `psiP R m J` is the polynomial `ψ_J` over a commutative ring `R` (same formula, with `X_a` for
  `t_a`); `psiP ℤ m J` is `ψ_J^ℤ`, and its image in `K[G]` is `ψ_J` (`mk_map_psiP_int`).
* `intMatU m k` is the integer matrix `A` of (i): rows indexed by `(ν, J)`, columns by
  `μ ∈ {0, …, m−1}^d`, entry `A_{(ν,J),μ} = Σ_{e ≡ μ (mod m)} b_e`, where
  `X^ν ψ_J^ℤ = Σ_e b_e X^e`. This sum is the coefficient of the group element `[μ]` of the image
  of `X^ν ψ_J^ℤ` in `ℤ[(ℤ/m)^d]` (`foldP`), which is how it is written here.
* `finrank_IK_eq_rankOver` is (i): `dim_K I_K = rank_K(A)` for every field `K` (`m ≥ 1`).
-/

@[expose] public section

open MvPolynomial

namespace ColUpper

open ColSplit ColSurv

set_option synthInstance.maxHeartbeats 200000

section Ring

variable (R : Type*) [CommRing R] (m : ℕ)

/-- **Proof of (i)** in `q_col_upper.md`: the variables `X_a ∈ R[X_1, …, X_d]` indexed by
`a ∈ V = Fin (2 * k + 2)` (for `a = j + 1` the variable `X j`; dummy value `0` at `a = 0`). -/
noncomputable def tP (k : ℕ) : Fin (2 * k + 2) → MvPolynomial (Fin (2 * k + 1)) R :=
  Fin.cases 0 X

/-- **Proof of (i)** in `q_col_upper.md`: the polynomial `ψ_J` over a commutative ring `R`,
`Π_{a < J(a)} (X_{J(a)} − 1) · Π_{0 < a < J(a)} φ(X_a X_{J(a)})`; for `R = ℤ` this is `ψ_J^ℤ`. -/
noncomputable def psiP {k : ℕ} (J : BallotBound.Matching k) : MvPolynomial (Fin (2 * k + 1)) R :=
  (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tP R k (J.1 a) - 1)) *
    ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), phi m (tP R k a * tP R k (J.1 a))

variable {R}

/-- **Proof of (i)** in `q_col_upper.md`: a ring map `R → S` sends `ψ_J` over `R` to `ψ_J` over
`S` (the formula is the same over every ring). -/
theorem map_psiP {S : Type*} [CommRing S] (f : R →+* S) {k : ℕ} (J : BallotBound.Matching k) :
    MvPolynomial.map f (psiP R m J) = psiP S m J := by
  have ht : ∀ a, MvPolynomial.map f (tP R k a) = tP S k a := by
    intro a
    cases a using Fin.cases <;> simp [tP]
  simp only [psiP, map_mul, map_prod, map_sub, map_one, map_phi, ht]

end Ring

variable {K : Type*} [Field K] {m : ℕ}

/-- **Proof of (i)** in `q_col_upper.md`: the image of `ψ_J` over `K` in `K[G]` is `ψ_J`. -/
theorem mk_psiP {k : ℕ} (J : BallotBound.Matching k) :
    Ideal.Quotient.mk (gaIdeal K (2 * k + 1) m) (psiP K m J) = psiG K m J := by
  have ht : ∀ a, Ideal.Quotient.mk (gaIdeal K (2 * k + 1) m) (tP K k a) = tU K m k a := by
    intro a
    cases a using Fin.cases <;> simp [tP, tU]
  simp only [psiP, psiG, map_mul, map_prod, map_sub, map_one, map_phi, ht]

/-- **Proof of (i)** in `q_col_upper.md`: the image of `ψ_J^ℤ ∈ ℤ[X_1, …, X_d]` in `K[G]` is
`ψ_J`. -/
theorem mk_map_psiP_int {k : ℕ} (J : BallotBound.Matching k) :
    Ideal.Quotient.mk (gaIdeal K (2 * k + 1) m) (MvPolynomial.map (Int.castRingHom K) (psiP ℤ m J))
      = psiG K m J := by
  rw [map_psiP, mk_psiP]

/-- **Proof of (i)** in `q_col_upper.md`: reduction of exponents mod `m` commutes with the ring
map `ℤ → K` on coefficients. -/
theorem foldP_map_int {d : ℕ} (p : MvPolynomial (Fin d) ℤ) :
    foldP K d m (MvPolynomial.map (Int.castRingHom K) p) =
      AddMonoidAlgebra.mapRangeRingHom _ (Int.castRingHom K) (foldP ℤ d m p) := by
  have h : ((foldP K d m).toRingHom.comp (MvPolynomial.map (Int.castRingHom K))) =
      (AddMonoidAlgebra.mapRangeRingHom _ (Int.castRingHom K)).comp (foldP ℤ d m).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [foldP, AddMonoidAlgebra.mapRangeRingHom]
    · intro i
      simp [foldP, AddMonoidAlgebra.mapRangeRingHom]
  exact congrArg (fun φ => φ p) h

/-- **Theorem (i)** of `q_col_upper.md`: there are finitely many matchings of `V` (so `A` has
finitely many rows). -/
instance finite_matching (k : ℕ) : Finite (BallotBound.Matching k) :=
  inferInstanceAs (Finite {J : Fin (2 * k + 2) → Fin (2 * k + 2) // ∀ x, J x ≠ x ∧ J (J x) = x})

variable (m) (k : ℕ)

/-- **Theorem (i)** of `q_col_upper.md`: the integer matrix `A`, depending only on `m` and `k`.
Rows are indexed by the pairs `(ν, J)` (`ν ∈ {0, …, m−1}^d`, `J` a matching of `V`), columns by
`μ ∈ {0, …, m−1}^d`, and `A_{(ν,J),μ} = Σ_{e ≡ μ (mod m)} b_e` where `X^ν ψ_J^ℤ = Σ_e b_e X^e`;
this is the coefficient of `[μ]` in the image of `X^ν ψ_J^ℤ` in `ℤ[(ℤ/m)^d]`. -/
noncomputable def intMatU :
    Matrix ((Fin (2 * k + 1) → Fin m) × BallotBound.Matching k) (Fin (2 * k + 1) → Fin m) ℤ :=
  fun x μ => foldP ℤ (2 * k + 1) m ((∏ i, X i ^ (x.1 i : ℕ)) * psiP ℤ m x.2) (expZ μ)

variable {m k}

/-- **Proof of (i)** in `q_col_upper.md`: the coordinates of `x ∈ K[G]` in the monomial basis of
(0) are the coefficients of `fold(x) ∈ K[(ℤ/m)^d]`. -/
theorem monoBasis_repr {d : ℕ} (hm : 0 < m) (x : GA K d m) (ν : Fin d → Fin m) :
    (monoBasis K d m hm).repr x ν = foldGA K d m x (expZ ν) := by
  have : (Finsupp.lapply ν).comp (monoBasis K d m hm).repr.toLinearMap =
      (Finsupp.lapply (expZ ν)).comp (foldGA K d m).toLinearMap := by
    refine (monoBasis K d m hm).ext fun ν' => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply]
    rw [show monoBasis K d m hm ν' = monoGA ν' from monoBasis_apply K d m hm ν']
    show _ = foldGA K d m (monoGA ν') (expZ ν)
    rw [foldGA_monoGA]
    by_cases h : ν' = ν
    · subst h; simp
    · simp [h, expZ_injective.ne h]
  exact congrArg (fun φ => φ x) this

/-- **Proof of (i)** in `q_col_upper.md`: in the basis of (0), the row `(ν, J)` of `A`, read in
`K`, is the coordinate vector of `t^ν ψ_J`. -/
theorem equivFun_row (hm : 0 < m) (ν : Fin (2 * k + 1) → Fin m) (J : BallotBound.Matching k) :
    (monoBasis K (2 * k + 1) m hm).equivFun (monoGA ν * psiG K m J) =
      fun μ => ((intMatU m k (ν, J) μ : ℤ) : K) := by
  funext μ
  rw [Module.Basis.equivFun_apply, monoBasis_repr, monoGA, ← mk_map_psiP_int, ← map_mul,
    foldGA_mk]
  have : (∏ i, X i ^ (ν i : ℕ) : MvPolynomial (Fin (2 * k + 1)) K) =
      MvPolynomial.map (Int.castRingHom K) (∏ i, X i ^ (ν i : ℕ)) := by simp
  rw [this, ← map_mul, foldP_map_int]
  rfl

/-- **Proof of (i)** in `q_col_upper.md`: `I_K` is the `K`-span of the elements `t^ν ψ_J`
(`ν ∈ {0, …, m−1}^d`, `J` a matching), since `K[G]` is spanned by the `t^ν`. -/
theorem IK_eq_span (hm : 0 < m) :
    (IK K m k).restrictScalars K =
      Submodule.span K (Set.range fun x : (Fin (2 * k + 1) → Fin m) × BallotBound.Matching k =>
        monoGA x.1 * psiG K m x.2) := by
  have htop : Submodule.span K (Set.range (monoGA (K := K) (d := 2 * k + 1) (m := m))) = ⊤ :=
    span_monomials_GA (F := K) _ m hm
  have hV : IK K m k = Submodule.span (GA K (2 * k + 1) m) (Set.range (psiG K m (k := k))) := rfl
  rw [hV, ← Submodule.span_smul_of_span_eq_top htop]
  congr 1
  ext x
  simp only [Set.mem_smul, Set.mem_range, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
    exact ⟨(a, J), rfl⟩
  · rintro ⟨⟨a, J⟩, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨J, rfl⟩, rfl⟩

/-- **Theorem (i)** of `q_col_upper.md`: for every field `K` and `m ≥ 1`,
`dim_K I_K = rank_K(A)`, where `A = intMatU m k` is the integer matrix of (i) (depending only on
`m` and `k`) and `rank_K(A)` is the rank of its image over `K` (`EveryField.rankOver`). -/
theorem finrank_IK_eq_rankOver (hm : 0 < m) :
    Module.finrank K ((IK K m k).restrictScalars K) = EveryField.rankOver K (intMatU m k) := by
  let e := (monoBasis K (2 * k + 1) m hm).equivFun
  have hrows : Set.range (fun x : (Fin (2 * k + 1) → Fin m) × BallotBound.Matching k =>
      monoGA x.1 * psiG K m x.2) =
      (e.symm : ((Fin (2 * k + 1) → Fin m) → K) →ₗ[K] GA K (2 * k + 1) m) ''
        Set.range ((intMatU m k).map (Int.castRingHom K)).row := by
    rw [← Set.range_comp]
    congr 1
    funext x
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.eq_symm_apply, equivFun_row]
    rfl
  rw [IK_eq_span hm, hrows, Submodule.span_image, LinearEquiv.finrank_map_eq,
    EveryField.rankOver, Matrix.rank_eq_finrank_span_row]

/-- **Theorem (i)** of `q_col_upper.md` (as stated): for `m ≥ 1` there is an integer matrix `A`,
depending only on `m` and `k`, such that `dim_K I_K = rank_K(A)` for every field `K`. (The matrix is
`intMatU m k`, see `finrank_IK_eq_rankOver`.) -/
theorem exists_intMat (hm : 0 < m) :
    ∃ A : Matrix ((Fin (2 * k + 1) → Fin m) × BallotBound.Matching k) (Fin (2 * k + 1) → Fin m) ℤ,
      ∀ (L : Type) [Field L],
        Module.finrank L ((IK L m k).restrictScalars L) = EveryField.rankOver L A :=
  ⟨intMatU m k, fun _ _ => finrank_IK_eq_rankOver hm⟩

end ColUpper

end
