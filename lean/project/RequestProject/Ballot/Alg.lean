module

public import RequestProject.Ballot.Defs

/-!
# Algebraic lemmas for the ballot lower bound (steps (i) and (iv) of `q3_ballot_lower_bound.md`)

Instead of the lexicographic order of the source we use the (equally effective) order by the
weight `∑ i ∈ U, w i` of a monomial; see `coeff_monomial_mul_prod_sub`.
-/

@[expose] public section

open MvPolynomial Finset

namespace BallotBound

/-- The algebra `C` of the **Setting** of `q3_ballot_lower_bound.md` is finite dimensional over
`F` (its dimension is `2^{n'}`; we only need finiteness). -/
instance alg_finite (F : Type*) [Field F] (k : ℕ) : Module.Finite F (Alg F k) := by
  set I := squaresIdeal F k
  have hs : Algebra.adjoin F (Set.range fun i => Ideal.Quotient.mkₐ F I (X i)) = ⊤ := by
    rw [Set.range_comp' (Ideal.Quotient.mkₐ F I) X, Algebra.adjoin_image, adjoin_range_X,
      Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective F I
  have hfin : Module.Finite F (Algebra.adjoin F (Set.range fun i => Ideal.Quotient.mkₐ F I (X i))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (R := F)
    (Set.finite_range fun i => Ideal.Quotient.mkₐ F I (X i)) (by
      rintro _ ⟨i, rfl⟩
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      have : (Ideal.Quotient.mkₐ F I (X i)) ^ 2 = 0 := by
        rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [this]; exact isIntegral_zero)
  exact Module.Finite.of_surjective
    (Algebra.adjoin F (Set.range fun i => Ideal.Quotient.mkₐ F I (X i))).val.toLinearMap
    (fun x => ⟨⟨x, hs ▸ Algebra.mem_top⟩, rfl⟩)

/-- Squarefree coefficients of elements of the ideal `(y_i^2)` vanish; this is why the monomials
`y_U` (`U ⊆ [n']`) are well defined in `C` (**Setting** of `q3_ballot_lower_bound.md`). -/
theorem coeff_eq_zero_of_mem_span_sq {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (Set.range fun i : σ => (X i ^ 2 : MvPolynomial σ R)))
    {m : σ →₀ ℕ} (hm : ∀ i, m i ≤ 1) : coeff m p = 0 := by
  have e : Set.range (fun i : σ => (X i ^ 2 : MvPolynomial σ R)) =
      (fun s => monomial s (1 : R)) '' Set.range (fun i => Finsupp.single i 2) := by
    ext; simp [X_pow_eq_monomial]
  rw [e, mem_ideal_span_monomial_image] at hp
  by_contra h
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := hp m (mem_support_iff.2 h)
  have h1 := hle i
  have h2 := hm i
  simp at h1
  omega

/-- Step (i) of `q3_ballot_lower_bound.md` (in weight form): for `w a < w (π a)` on `A`, the
polynomial `X^Q · ∏_{a ∈ A} (X_{π a} − X_a)` has coefficient `(−1)^{|A|}` at the monomial
`X^Q · ∏_{a ∈ A} X_a` (choose `−X_a` in every factor), and every other monomial of weight at
most the weight of that one has coefficient `0`. -/
theorem coeff_monomial_mul_prod_sub {σ R : Type*} [CommRing R] [DecidableEq σ] (w : σ → ℕ)
    (π : σ → σ) (A : Finset σ) (hA : ∀ a ∈ A, w a < w (π a)) (Q m : σ →₀ ℕ)
    (hm : Finsupp.weight w m ≤ Finsupp.weight w (Q + ∑ a ∈ A, Finsupp.single a 1)) :
    coeff m (monomial Q (1 : R) * ∏ a ∈ A, (X (π a) - X a)) =
      if m = Q + ∑ a ∈ A, Finsupp.single a 1 then (-1) ^ A.card else 0 := by
  induction A using Finset.induction_on generalizing Q with
  | empty => simp [coeff_monomial, eq_comm]
  | insert a A ha ih =>
    have hA' : ∀ b ∈ A, w b < w (π b) := fun b hb => hA b (mem_insert_of_mem hb)
    have hwa := hA a (mem_insert_self a A)
    have hws : ∀ x : σ, Finsupp.weight w (Finsupp.single x 1) = w x := fun x => by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [prod_insert ha]
    have e : monomial Q (1 : R) * ((X (π a) - X a) * ∏ b ∈ A, (X (π b) - X b)) =
        monomial (Q + Finsupp.single (π a) 1) 1 * ∏ b ∈ A, (X (π b) - X b) -
          monomial (Q + Finsupp.single a 1) 1 * ∏ b ∈ A, (X (π b) - X b) := by
      have h1 : monomial (Q + Finsupp.single (π a) 1) (1 : R) = monomial Q 1 * X (π a) := by
        rw [X, monomial_mul, one_mul]
      have h2 : monomial (Q + Finsupp.single a 1) (1 : R) = monomial Q 1 * X a := by
        rw [X, monomial_mul, one_mul]
      rw [h1, h2]
      ring
    rw [e, coeff_sub, sum_insert ha]
    rw [sum_insert ha, map_add, map_add, hws] at hm
    rw [ih hA' (Q + Finsupp.single (π a) 1) (by rw [map_add, map_add, hws]; omega),
      ih hA' (Q + Finsupp.single a 1) (by rw [map_add, map_add, hws]; omega)]
    have hne : m ≠ Q + Finsupp.single (π a) 1 + ∑ b ∈ A, Finsupp.single b 1 := by
      intro h
      rw [h, map_add, map_add, hws] at hm
      omega
    rw [if_neg hne, card_insert_of_notMem ha, ← add_assoc]
    split_ifs <;> ring

/-- Step (iv) of `q3_ballot_lower_bound.md`: elements of `C` with pairwise distinct squarefree
leading monomials (here: minimal-weight monomials, in the triangular sense) are linearly
independent over `F`. -/
theorem linearIndependent_of_triangular {σ ι F : Type*} [Field F] (w : σ → ℕ)
    (v : ι → MvPolynomial σ F) (M : ι → σ →₀ ℕ) (hM : Function.Injective M)
    (hsq : ∀ i j, M i j ≤ 1) (hlead : ∀ i, coeff (M i) (v i) ≠ 0)
    (htri : ∀ i m, m ≠ M i → Finsupp.weight w m ≤ Finsupp.weight w (M i) → coeff m (v i) = 0) :
    LinearIndependent F (fun i => Ideal.Quotient.mkₐ F
      (Ideal.span (Set.range fun j : σ => (X j ^ 2 : MvPolynomial σ F))) (v i)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hne
  set s' := s.filter (fun i => g i ≠ 0)
  have hs' : s'.Nonempty := ⟨i, mem_filter.2 ⟨hi, hne⟩⟩
  obtain ⟨i0, hi0, hmin⟩ := s'.exists_min_image (fun i => Finsupp.weight w (M i)) hs'
  have hmem : ∑ i ∈ s, g i • v i ∈
      Ideal.span (Set.range fun j : σ => (X j ^ 2 : MvPolynomial σ F)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk F, map_sum]
    simpa only [map_smul] using hsum
  have h0 := coeff_eq_zero_of_mem_span_sq hmem (hsq i0)
  rw [coeff_sum, sum_eq_single i0] at h0
  · rw [coeff_smul, smul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact (mem_filter.1 hi0).2 h
    · exact hlead i0 h
  · intro j hj hji0
    rw [coeff_smul]
    by_cases hg : g j = 0
    · simp [hg]
    · rw [htri j (M i0) (fun h => hji0 (hM h).symm) (hmin j (mem_filter.2 ⟨hj, hg⟩)),
        smul_zero]
  · intro h; exact absurd (mem_filter.1 hi0).1 h

end BallotBound

end
