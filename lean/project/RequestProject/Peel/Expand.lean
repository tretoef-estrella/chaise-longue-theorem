module

public import RequestProject.Peel.Defs

/-!
# Basic facts on the expansion `f = Σ_j f_j y_1^j` (`q_peeling_lemma.md`)

Auxiliary facts about the unique expansion of the **Setting** of `q_peeling_lemma.md`, stated for
an arbitrary `F`-algebra `R` in place of `C_{m−1}`, used in the proof of the **Lemma (peeling)**.
-/

@[expose] public section

open Polynomial

namespace Peel

variable {F : Type*} [Field F] {q : ℕ} {R : Type*} [CommRing R] [Algebra F R]

/-- The expansion recovers the element (uniqueness of the expansion in the **Setting** of
`q_peeling_lemma.md`).
Used in part (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem mk_expandGen (x : Peeled q R) : AdjoinRoot.mk _ (expandGen F q R x) = x :=
  AdjoinRoot.mk_leftInverse (monic_X_pow_q q R) x

/-- The expansion map is injective (uniqueness of the expansion in the **Setting** of
`q_peeling_lemma.md`).
Used in part (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem expandGen_injective : Function.Injective (expandGen F q R) :=
  (AdjoinRoot.mk_leftInverse (monic_X_pow_q q R)).injective

/-- The expansion has degree `≤ q − 2` (it is `Σ_{j=0}^{q−2} f_j y_1^j`), as in the **Setting** of
`q_peeling_lemma.md`.
Used in part (iii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem degree_expandGen_le (hq : 1 ≤ q) (x : Peeled q R) :
    (expandGen F q R x).degree ≤ ((q - 2 : ℕ) : WithBot ℕ) := by
  nontriviality R
  have hx : expandGen F q R x = expandGen F q R x %ₘ (X ^ (q - 1) : R[X]) := by
    have := AdjoinRoot.modByMonicHom_mk (monic_X_pow_q q R) (expandGen F q R x)
    rw [mk_expandGen] at this
    exact this
  have h := Polynomial.degree_modByMonic_lt (expandGen F q R x) (monic_X_pow_q q R)
  rw [← hx, degree_X_pow, degree_lt_iff_coeff_zero] at h
  rw [degree_le_iff_coeff_zero]
  intro m hm
  apply h
  have : q - 2 < m := by exact_mod_cast hm
  exact_mod_cast (show q - 1 ≤ m by omega)

/-- Multiplying by `y_1` raises the degree by at most one (used in part (ii) of the proof in
`q_peeling_lemma.md`).
Used in part (ii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem degree_X_mul_le (p : R[X]) (j : ℕ) (h : p.degree ≤ j) : (X * p).degree ≤ ↑(j + 1) := by
  rw [degree_le_iff_coeff_zero] at *
  intro m hm
  rcases m with _ | m
  · simp
  · rw [coeff_X_mul]; apply h; have : j + 1 < m + 1 := by exact_mod_cast hm
    exact_mod_cast (show j < m by omega)

/-- Multiplying by a constant `g ∈ C_{m−1}` multiplies the expansion by `g`
(used in part (i) of the proof in `q_peeling_lemma.md`).
Used in part (i) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem expandGen_of_mul (g : R) (x : Peeled q R) :
    expandGen F q R (AdjoinRoot.of _ g * x) = Polynomial.C g * expandGen F q R x := by
  rw [← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def, ← Polynomial.smul_eq_C_mul]
  exact (AdjoinRoot.modByMonicHom (monic_X_pow_q q R)).map_smul g x

/-- Multiplying by `y_1` shifts the expansion when there is no wrap-around
(used in part (ii) of the proof in `q_peeling_lemma.md`).
Used in part (ii) of the Lemma (peeling) of `q_peeling_lemma.md`. -/
theorem expandGen_root_mul (x : Peeled q R) (j : ℕ)
    (hx : (expandGen F q R x).degree ≤ j) (hj : j < q - 2) :
    expandGen F q R (AdjoinRoot.root _ * x) = Polynomial.X * expandGen F q R x := by
  nontriviality R
  conv_lhs => rw [← mk_expandGen (F := F) x]
  rw [← AdjoinRoot.mk_X, ← map_mul]
  change AdjoinRoot.modByMonicHom (monic_X_pow_q q R) _ = _
  rw [AdjoinRoot.modByMonicHom_mk, modByMonic_eq_self_iff (monic_X_pow_q q R), degree_X_pow]
  have h := degree_X_mul_le _ j hx
  rw [degree_le_iff_coeff_zero] at h
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  apply h
  have : q - 1 ≤ m := by exact_mod_cast hm
  exact_mod_cast (show j + 1 < m by omega)

end Peel

end
