module

public import RequestProject.Pow2.Theta
public import RequestProject.Pow2.Lowest
public import RequestProject.Odd3.Main
public import RequestProject.EvenCount.Main
public import RequestProject.Degeneration.Main

/-!
# Degree `2^v`: Proposition 9.2 and its consequences (`q_pow2_leading.md`, (vi)–(ix))

This file proves parts **(vi)**, **(vii)**, **(viii)** and **(ix)** of the **Theorem** of
`q_pow2_leading.md`.

* **(vi)** `prop92_ge`: `dim_F (D_J : J ∈ 𝒥)·C ≤ dim_F I_F`, from (ii), (iii), (iv), (v) and
  Proposition 2.5 (ii) of `q_col_one.md` (`ColOne.lemma25_ii`), as in the **Proof** of (vi).
  The leading-form argument (`P_J = L_J + (terms of degree > δ)`, `L_J` homogeneous of degree `δ`)
  is carried out with the predicate `Pow2.Lead`.
* **(vii)** `quartic_char_two`, **(viii)** `pow2_of_oddbox`, **(ix)** `dim_DIdeal_two`,
  `QkEven_two`, `dim_IK_two`.

Dimensions are `Module.finrank F` of ideals regarded as `F`-subspaces (`restrictScalars F`).
-/

@[expose] public section

open MvPolynomial

namespace Pow2

set_option synthInstance.maxHeartbeats 200000

/-! ### Leading forms -/

section Lead

variable {σ R : Type*} [CommRing R]

/-- **Proof of (vi)** of `q_pow2_leading.md`: `g` is the lowest form of `p` in degree `n`, i.e.
`g` is homogeneous of degree `n` and every monomial of `p − g` has degree `> n`. -/
def Lead (p g : MvPolynomial σ R) (n : ℕ) : Prop :=
  g.IsHomogeneous n ∧ p - g ∈ ordGE σ R (n + 1)

/-- **Proof of (vi)** of `q_pow2_leading.md`: a homogeneous polynomial is its own lowest form. -/
theorem Lead.refl {g : MvPolynomial σ R} {n : ℕ} (hg : g.IsHomogeneous n) : Lead g g n :=
  ⟨hg, by rw [sub_self]; exact Submodule.zero_mem _⟩

/-- **Proof of (vi)** of `q_pow2_leading.md`: lowest forms multiply. -/
theorem Lead.mul {p g p' g' : MvPolynomial σ R} {n n' : ℕ} (h : Lead p g n) (h' : Lead p' g' n') :
    Lead (p * p') (g * g') (n + n') := by
  refine ⟨h.1.mul h'.1, ?_⟩
  have hp' : p' ∈ ordGE σ R n' := by
    have : p' = g' + (p' - g') := by ring
    rw [this]
    exact Submodule.add_mem _ (IsHomogeneous.mem_ordGE' h'.1) (ordGE_mono (by omega) h'.2)
  have e : p * p' - g * g' = (p - g) * p' + g * (p' - g') := by ring
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · have := mul_mem_ordGE h.2 hp'
    rwa [show n + 1 + n' = n + n' + 1 by omega] at this
  · have := mul_mem_ordGE (IsHomogeneous.mem_ordGE' h.1) h'.2
    rwa [← add_assoc] at this

/-- **Proof of (vi)** of `q_pow2_leading.md`: lowest forms of powers. -/
theorem Lead.pow {p g : MvPolynomial σ R} {n : ℕ} (h : Lead p g n) (j : ℕ) :
    Lead (p ^ j) (g ^ j) (n * j) := by
  induction j with
  | zero => simpa using Lead.refl (isHomogeneous_one σ R)
  | succ j ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact ih.mul h

/-- **Proof of (vi)** of `q_pow2_leading.md`: lowest forms of finite products. -/
theorem Lead.prod {ι : Type*} (s : Finset ι) {p g : ι → MvPolynomial σ R} {n : ι → ℕ}
    (h : ∀ i ∈ s, Lead (p i) (g i) (n i)) :
    Lead (∏ i ∈ s, p i) (∏ i ∈ s, g i) (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lead.refl (isHomogeneous_one σ R)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Proof of (vi)** of `q_pow2_leading.md`: the lowest form of `s_a + s_b + s_a s_b` is
`s_a + s_b`. -/
theorem Lead.lin (a b : σ) : Lead (X a + X b + X a * X b : MvPolynomial σ R) (X a + X b) 1 := by
  refine ⟨(isHomogeneous_X R a).add (isHomogeneous_X R b), ?_⟩
  rw [add_sub_cancel_left]
  exact IsHomogeneous.mem_ordGE' ((isHomogeneous_X R a).mul (isHomogeneous_X R b))

end Lead

variable (F : Type*) [Field F]

/-- **Proof of (vi)** of `q_pow2_leading.md`: for every matching `J`, `L_J` is the lowest form of
`P_J` (`P_J = L_J + (terms of degree > δ)`, `L_J` homogeneous of degree `δ`). -/
theorem lead_PJ_LJ (q : ℕ) {k : ℕ} (J : BallotBound.Matching k) :
    Lead (PJ F q J) (LJ F q J)
      ((∑ _a ∈ Finset.univ.filter (fun a => a < J.1 a), 1) +
        ∑ _a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a), 1 * (q - 1)) := by
  rw [PJ, LJ]
  refine (Lead.prod _ fun a _ => Lead.refl (isHomogeneous_X F _)).mul
    (Lead.prod _ fun a _ => (Lead.lin _ _).pow _)

/-! ### (vi) Proposition 9.2 -/

variable {F}

/-- **Proof of (vi)** of `q_pow2_leading.md`: `Θ(I_F) = (P̄_J : J)·B` (by (iii)), so
`dim_F I_F = dim_F (P̄_J : J)·B` (by (ii)). -/
theorem finrank_IK_eq_span_PJ [CharP F 2] (v k : ℕ) :
    Module.finrank F ((ColUpper.IK F (2 ^ v) k).restrictScalars F) =
      Module.finrank F ((Ideal.span (Set.range fun J : BallotBound.Matching k =>
        Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (PJ F (2 ^ v) J))).restrictScalars
          F) := by
  set Θ := Theta F (2 * k + 1) v
  have hmap : Ideal.span (Set.range fun J : BallotBound.Matching k =>
      Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (PJ F (2 ^ v) J)) =
      (ColUpper.IK F (2 ^ v) k).map Θ := by
    rw [ColUpper.IK, Ideal.map_span, ← Set.range_comp]
    congr 1
    refine congrArg Set.range (funext fun J => ?_)
    exact (Theta_psiG v J).symm
  have hsub : ((ColUpper.IK F (2 ^ v) k).map Θ).restrictScalars F =
      ((ColUpper.IK F (2 ^ v) k).restrictScalars F).map (Θ.toLinearEquiv : _ →ₗ[F] _) := by
    ext y
    rw [Submodule.restrictScalars_mem, Ideal.mem_map_of_equiv, Submodule.mem_map]
    rfl
  rw [hmap, hsub, LinearEquiv.finrank_map_eq]

/-- **(vi) (Proposition 9.2, the inequality)** of `q_pow2_leading.md`: for every field `F` of
characteristic `2`, every `v ≥ 1` (`q = 2^v`) and every `k`,
`dim_F (D_J : J ∈ 𝒥)·C ≤ dim_F I_F`. -/
theorem prop92_ge (F : Type*) [Field F] [CharP F 2] {v : ℕ} (hv : 1 ≤ v) (k : ℕ) :
    Module.finrank F ((TheoremB.DIdeal F (2 ^ v) k).restrictScalars F) ≤
      Module.finrank F ((ColUpper.IK F (2 ^ v) k).restrictScalars F) := by
  rw [finrank_IK_eq_span_PJ]
  -- (iv) with `e = q`, `f_J = P_J`, `g_J = L_J`
  have h4 := lowest_forms (2 ^ v) (Ideal.span (Set.range fun J : BallotBound.Matching k =>
      Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (PJ F (2 ^ v) J)))
    (fun J => PJ F (2 ^ v) J) (fun J => LJ F (2 ^ v) J) _
    (fun J => Ideal.subset_span ⟨J, rfl⟩) (fun J => (lead_PJ_LJ F (2 ^ v) J).1)
    (fun J s hs => (mem_ordGE.1 (lead_PJ_LJ F (2 ^ v) J).2) s hs)
  refine le_trans (le_of_eq ?_) h4
  -- (v)(b) and Proposition 2.5 (ii)
  have hL : (fun J : BallotBound.Matching k =>
      Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (LJ F (2 ^ v) J)) =
      fun J => ColOne.Ym F (2 ^ v) (2 * k + 1) *
        Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v + 1) (2 * k + 1)) (EJ F (2 ^ v) J) :=
    funext fun J => mk_LJ hv J
  have hD : TheoremB.DIdeal F (2 ^ v) k = Ideal.span (Set.range fun J : BallotBound.Matching k =>
      Ideal.Quotient.mk (Peel.powIdeal F (2 ^ v) (2 * k + 1)) (EJ F (2 ^ v) J)) := by
    rw [TheoremB.DIdeal]
    congr 1
    exact congrArg Set.range (funext fun J => (mk_EJ F (2 ^ v) J).symm)
  rw [hL, ColOne.lemma25_ii, hD]

/-! ### (vii), (viii), (ix) -/

/-- **(viii) (the conditional form)** of `q_pow2_leading.md`: for `v ≥ 1`, `q = 2^v`, a field `F`
of characteristic `2` and `k ≥ 0`: if `Q^e_k(q) ≤ dim_F (D_J : J ∈ 𝒥)·C`, then
`dim_F I_F = Q^e_k(q)`. -/
theorem pow2_of_oddbox (F : Type*) [Field F] [CharP F 2] {v : ℕ} (hv : 1 ≤ v) (k : ℕ)
    (h : EvenCount.QkEven k (2 ^ v) ≤
      Module.finrank F ((TheoremB.DIdeal F (2 ^ v) k).restrictScalars F)) :
    Module.finrank F ((ColUpper.IK F (2 ^ v) k).restrictScalars F) =
      EvenCount.QkEven k (2 ^ v) := by
  have h2 : 2 ≤ 2 ^ v := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  have heven : Even (2 ^ v) := (Nat.even_pow' (by omega)).2 even_two
  exact le_antisymm (EvenCount.finrank_IK_le_even F heven h2 k) (h.trans (prop92_ge F hv k))

/-- **(vii) (the quartic, at the prime `2`)** of `q_pow2_leading.md`: for every field `F` of
characteristic `2` and every `k ≥ 0`, with `m = q = 4`: `dim_F I_F = Q^e_k(4)`. -/
theorem quartic_char_two (F : Type*) [Field F] [CharP F 2] (k : ℕ) :
    Module.finrank F ((ColUpper.IK F 4 k).restrictScalars F) = EvenCount.QkEven k 4 :=
  pow2_of_oddbox F (v := 2) (by norm_num) k (Odd3.O_ge_three F k)

/-- **Proof of (ix)** of `q_pow2_leading.md`: a matching of `{0, 1, …, 2k+1}` (the pairs
`{2i, 2i + 1}`), so that `𝒥` is nonempty. -/
def pairMatching (k : ℕ) : BallotBound.Matching k :=
  ⟨fun a => ⟨if a.val % 2 = 0 then a.val + 1 else a.val - 1, by split_ifs <;> omega⟩, fun a => by
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      split_ifs at this <;> omega
    · simp only
      split_ifs <;> omega⟩

/-- **(ix) (`q = 2`)** of `q_pow2_leading.md`, first claim: for every field `F` (of any
characteristic) and every `k ≥ 0`, `dim_F (D_J : J ∈ 𝒥)·C = 1` at `q = 2` (here `C = F` and
`D_J = 1`). -/
theorem dim_DIdeal_two (F : Type*) [Field F] (k : ℕ) :
    Module.finrank F ((TheoremB.DIdeal F 2 k).restrictScalars F) = 1 := by
  have hD : ∀ J : BallotBound.Matching k, TheoremB.DJ F 2 J = 1 := by
    intro J
    simp [TheoremB.DJ, Tight.D]
  have htop : TheoremB.DIdeal F 2 k = ⊤ :=
    (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨pairMatching k, hD _⟩)
  rw [htop, Submodule.restrictScalars_top, finrank_top, Degeneration.finrank_C le_rfl]
  simp

/-- **(ix) (`q = 2`)** of `q_pow2_leading.md`, second claim: `Q^e_k(2) = 1` (here `(m − 2)/2 = 0`
and the only term has `2c = 2k + 2`). -/
theorem QkEven_two (k : ℕ) : EvenCount.QkEven k 2 = 1 := by
  rw [EvenCount.QkEven, Finset.sum_eq_single (k + 1)]
  · simp only [show 2 * (k + 1) = 2 * k + 2 by ring]
    simp [Nat.div_self (Nat.factorial_pos _)]
  · intro c _ hc
    simp
    omega
  · intro h
    simp at h

/-- **(ix) (`q = 2`)** of `q_pow2_leading.md`, third claim: for every field `F` of characteristic
`2` and every `k ≥ 0`, with `m = q = 2`: `dim_F I_F = 1` (by (viii)). -/
theorem dim_IK_two (F : Type*) [Field F] [CharP F 2] (k : ℕ) :
    Module.finrank F ((ColUpper.IK F 2 k).restrictScalars F) = 1 := by
  have h := pow2_of_oddbox F (v := 1) le_rfl k (by
    rw [pow_one, QkEven_two, dim_DIdeal_two])
  rwa [pow_one, QkEven_two] at h

/-- **(ix) (`q = 2`)** of `q_pow2_leading.md`, all three claims: for every field `F` of
characteristic `2` and every `k ≥ 0`, with `m = q = 2`: `dim_F (D_J : J ∈ 𝒥)·C = 1`,
`Q^e_k(2) = 1` and `dim_F I_F = 1`. -/
theorem q_two (F : Type*) [Field F] [CharP F 2] (k : ℕ) :
    Module.finrank F ((TheoremB.DIdeal F 2 k).restrictScalars F) = 1 ∧
      EvenCount.QkEven k 2 = 1 ∧
      Module.finrank F ((ColUpper.IK F 2 k).restrictScalars F) = 1 :=
  ⟨dim_DIdeal_two F k, QkEven_two k, dim_IK_two F k⟩

end Pow2

end
