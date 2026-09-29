module

public import RequestProject.ColOne.Gen

/-!
# Transport of `I_{c,1}` to the coordinates `y` (`q_col_one.md`, proof of Lemma 6.6 (ii), (iii))

This file contains the common part of the **Proof** of Lemma 6.6 (ii) and (iii) of
`q_col_one.md`: for an increasing bijection `ē : ι → 𝒞_1` from a finite linearly ordered set `ι`
and a bijection `e : [n] → W_1` compatible with it, the perfect matchings `P` of `𝒞_1` are the
`ē ∘ P' ∘ ē^{−1}` for the perfect matchings `P'` of `ι`, `D_P = Ψ_e(D_{P'})`, and hence (by
Lemma 2.4 (ii), Lemma 6.4 (v) in the form `span_eq_of_units`, Lemma 2.3 (i) and Proposition 2.5 (ii))
`dim I_{c,1} = dim (D_{P'} : P')·C_n`.
-/

@[expose] public section

open MvPolynomial

namespace ColOne

open ColSplit ColSurv ColComp ColTensor ColDecomp Peel

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F) {k : ℕ}

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {c : Fin (2 * k + 1) → S.μ}

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: the perfect matching
`ē ∘ P' ∘ ē^{−1}` of `𝒞_1` obtained from a perfect matching `P'` of `ι` and a bijection
`ē : ι → 𝒞_1`. -/
def conjPM (ē : ι ≃o cls (cExt c) 1) (P : PerfMatch ι) : PerfMatch (cls (cExt c) 1) :=
  ⟨fun x => ē (P.1 (ē.symm x)), fun x => by
    refine ⟨fun h => (P.2 (ē.symm x)).1 ?_, ?_⟩
    · have := congrArg ē.symm h
      simpa using this
    · simp [(P.2 _).2]⟩

omit [Fintype ι] in
/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: every perfect matching of `𝒞_1` is of the
form `ē ∘ P' ∘ ē^{−1}`. -/
theorem conjPM_surjective (ē : ι ≃o cls (cExt c) 1) :
    Function.Surjective (conjPM S ē) := by
  intro P
  refine ⟨⟨fun a => ē.symm (P.1 (ē a)), fun a => ?_⟩, ?_⟩
  · refine ⟨fun h => (P.2 (ē a)).1 ?_, ?_⟩
    · have := congrArg ē h
      simpa using this
    · simp [(P.2 _).2]
  · exact PerfMatch.ext fun x => by simp [conjPM]

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: the polynomial
`D_{P'} = Π D(y_{κ(a)}, y_{κ(b)}) ∈ F[y_1, …, y_n]` over the pairs `{a < b}` of a perfect matching
`P'` of `ι` with `ē(a) ≠ 0`, where `κ : ι → [n]` gives the variable attached to each index. -/
noncomputable def fpoly (ē : ι ≃o cls (cExt c) 1) {n : ℕ} (κ : ι → Fin n) (P : PerfMatch ι) :
    MvPolynomial (Fin n) F :=
  ∏ a ∈ Finset.univ.filter (fun a => (ē a).1 ≠ 0 ∧ a < P.1 a),
    Dab S.q (X (κ a)) (X (κ (P.1 a)))

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: the isomorphism
`Ψ_e : B_n → B(W_1)` of Lemma 2.3 (i) for the block `W_1` (a box ring at the point `1`, with
exponent `q`), for a bijection `e : [n] → W_1`. -/
noncomputable def PsiW (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ} (e : Fin n ≃ W1 S c) :
    C F (S.q + 1) n ≃ₐ[F] (boxS S c).Box (W1 S c) :=
  Psi S hp rfl (boxS_c_W1 S c) e

/-- **Lemma 2.3 (i)** of `q_col_one.md` for the block `W_1`: `Ψ_e(y_i) = y_{e(i)}`. -/
theorem PsiW_X (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ} (e : Fin n ≃ W1 S c)
    (i : Fin n) :
    PsiW S hp c e (Ideal.Quotient.mk _ (X i)) = yW (boxS S c) (W1 S c) (e i) :=
  Psi_X S hp rfl (boxS_c_W1 S c) e i

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: `Ψ_e(Y_n) = Y_{W_1}`. -/
theorem Psi_Ym (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) {n : ℕ} (e : Fin n ≃ W1 S c) :
    PsiW S hp c e (Ym F S.q n) = YW (boxS S c) (W1 S c) := by
  rw [Ym, map_prod, YW]
  simp only [Tight.y, PsiW_X]
  exact Fintype.prod_equiv e _ _ fun _ => rfl

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: since `ē` is increasing and compatible
with `e`, `Ψ_e(D_{P'}) = D_P` for `P = ē ∘ P' ∘ ē^{−1}`. -/
theorem Psi_fpoly (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) (ē : ι ≃o cls (cExt c) 1) {n : ℕ}
    (e : Fin n ≃ W1 S c) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) (P : PerfMatch ι) :
    PsiW S hp c e (Ideal.Quotient.mk _ (fpoly S ē κ P)) =
      DP S c (conjPM S ē P) := by
  have hy : ∀ a, (ē a).1 ≠ 0 →
      PsiW S hp c e (Ideal.Quotient.mk _ (X (κ a))) = yB S c (W1 S c) (ē a).1 := by
    intro a ha
    rw [PsiW_X, ← hκ a ha, yB_succ S c _ (e (κ a)).2]
  rw [fpoly, map_prod, map_prod, DP]
  refine Finset.prod_equiv ē.toEquiv ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ (ē a).1 ≠ 0 ∧ (ē a).1 < (ē (P.1 (ē.symm (ē a)))).1
    rw [Subtype.coe_lt_coe, ē.symm_apply_apply, ē.lt_iff_lt]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hPa : (ē (P.1 a)).1 ≠ 0 := by
      have : (ē a).1 < (ē (P.1 a)).1 := by rw [Subtype.coe_lt_coe, ē.lt_iff_lt]; exact ha.2
      exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) this)
    rw [map_Dab, map_Dab, hy a ha.1, hy _ hPa]
    simp [conjPM]

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: `I_{c,1} = Ψ_e((Y_n D_{P'} : P')·B_n)`
(the generators `g_P = u·Y_{W_1}·D_P` of Lemma 2.4 (ii) and `Ψ_e(Y_n D_{P'}) = Y_{W_1}·D_P` agree up
to units, which do not change the ideal). -/
theorem Ic1_eq_map (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) (ē : ι ≃o cls (cExt c) 1) {n : ℕ}
    (e : Fin n ≃ W1 S c) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) :
    Ic1 S c = (Ideal.span (Set.range fun P : PerfMatch ι =>
      Ym F S.q n * Ideal.Quotient.mk _ (fpoly S ē κ P))).map (PsiW S hp c e) := by
  have hΨ : ∀ P : PerfMatch ι, PsiW S hp c e
      (Ym F S.q n * Ideal.Quotient.mk _ (fpoly S ē κ P)) =
        YW (boxS S c) (W1 S c) * DP S c (conjPM S ē P) := by
    intro P
    rw [map_mul, Psi_Ym, Psi_fpoly S hp c ē e κ hκ]
  rw [Ideal.map_span, ← Set.range_comp, Ic1]
  apply ColPairs.span_eq_of_units
  · rintro _ ⟨P, rfl⟩
    obtain ⟨P', rfl⟩ := conjPM_surjective S ē P
    obtain ⟨u, hu⟩ := lemma24_ii S hp c (conjPM S ē P')
    exact ⟨_, ⟨P', rfl⟩, u, by rw [hu, Function.comp_apply, hΨ]⟩
  · rintro _ ⟨P', rfl⟩
    obtain ⟨u, hu⟩ := lemma24_ii S hp c (conjPM S ē P')
    exact ⟨_, ⟨conjPM S ē P', rfl⟩, u, by rw [hu, Function.comp_apply, hΨ]⟩

/-- **Proof of Lemma 6.6 (ii), (iii)** of `q_col_one.md`: `dim_F I_{c,1} = dim_F (D_{P'} : P')·C_n`
(`Ψ_e` is an `F`-algebra isomorphism, and Proposition 2.5 (ii)). -/
theorem finrank_Ic1_eq (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) (ē : ι ≃o cls (cExt c) 1)
    {n : ℕ} (e : Fin n ≃ W1 S c) (κ : ι → Fin n)
    (hκ : ∀ a, (ē a).1 ≠ 0 → (e (κ a)).1.succ = (ē a).1) :
    Module.finrank F (Ic1 S c) =
      Module.finrank F ((Ideal.span (Set.range fun P : PerfMatch ι =>
        Ideal.Quotient.mk (powIdeal F S.q n) (fpoly S ē κ P))).restrictScalars F) := by
  rw [Ic1_eq_map S hp c ē e κ hκ, ColPairs.finrank_map_algEquiv]
  exact lemma25_ii n (fpoly S ē κ)

end ColOne

end
