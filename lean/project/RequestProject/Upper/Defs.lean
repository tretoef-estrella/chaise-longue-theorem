module

public import RequestProject.Ballot.Alg

/-!
# Polynomial lifts and evaluation on `{1, −1}` (`q3_upper_bound.md`)

This file sets up the objects of the **Proof of the Theorem** of `q3_upper_bound.md`:
the ring `S = F[y_1, …, y_{n'}]` (here `MvPolynomial (Fin (2 * k + 1)) F`), the polynomials
`g_J ∈ S` lifting `D_J`, the ideal they generate, the points of `T^{n'}` with `T = {1, −1}`, and
the support `Σ` of step (ii).
-/

@[expose] public section

open MvPolynomial Finset

namespace BallotBound

variable (F : Type*) [Field F] (k : ℕ)

/-- The polynomial lifts `y_i ∈ S` of the generators `y_i ∈ C` (see `BallotBound.y`), indexed by
the ground set `{0, 1, …, n'}`; the value at `0` is an unused dummy value `0`.
(Beginning of the **Proof of the Theorem** of `q3_upper_bound.md`.) -/
noncomputable def yP : Fin (2 * k + 2) → MvPolynomial (Fin (2 * k + 1)) F :=
  Fin.cases 0 X

variable {F k} in
/-- The polynomial `g_J = ∏_{(a,b)} (y_b − y_a) ∈ S` of the **Proof of the Theorem** of
`q3_upper_bound.md`: the same product as `D_J`, before passing to `C`. -/
noncomputable def g (J : Matching k) : MvPolynomial (Fin (2 * k + 1)) F :=
  ∏ a ∈ Finset.univ.filter (fun a => a ≠ 0 ∧ J.1 a ≠ 0 ∧ a < J.1 a), (yP F k (J.1 a) - yP F k a)

/-- The ideal `(g_J : J ∈ 𝒥) ⊆ S` (the first summand of the ideal `I` of step (iii) of
`q3_upper_bound.md`). -/
noncomputable def G : Ideal (MvPolynomial (Fin (2 * k + 1)) F) :=
  Ideal.span (Set.range (g (F := F) (k := k)))

/-- The point of `T^{n'}`, `T = {1, −1}`, attached to a set `A ⊆ {1, …, n'}`: its coordinates
are `1` on `A` and `−1` off `A` (step (i) of `q3_upper_bound.md`).  Every point of `T^{n'}`
is of this form. -/
def pt (A : Finset (Fin (2 * k + 1))) : Fin (2 * k + 1) → F :=
  fun i => if i ∈ A then 1 else -1

open Classical in
/-- The support `Σ := {z ∈ T^{n'} : g_J(z) ≠ 0 for some J ∈ 𝒥}` of step (ii) of
`q3_upper_bound.md`, with points of `T^{n'}` encoded by the sets `A` of coordinates equal
to `1` (see `BallotBound.pt`). -/
noncomputable def supp : Finset (Finset (Fin (2 * k + 1))) :=
  Finset.univ.filter (fun A => ∃ J : Matching k, eval (pt F k A) (g J) ≠ 0)

variable {F k} in
/-- The ideal `(y_1^2, …, y_{n'}^2)` of the **Setting** is a monomial ideal: a polynomial lies in
it iff each of its monomials is divisible by some `y_i^2`.  (Used in steps (iv) and (v) of
`q3_upper_bound.md`.) -/
theorem mem_squaresIdeal_iff {p : MvPolynomial (Fin (2 * k + 1)) F} :
    p ∈ squaresIdeal F k ↔ ∀ m ∈ p.support, ∃ i, 2 ≤ m i := by
  classical
  have e : Set.range (fun i : Fin (2 * k + 1) => (X i ^ 2 : MvPolynomial (Fin (2 * k + 1)) F)) =
      (fun s => monomial s (1 : F)) '' Set.range (fun i => Finsupp.single i 2) := by
    ext; simp [X_pow_eq_monomial]
  rw [squaresIdeal, e, mem_ideal_span_monomial_image]
  refine forall₂_congr fun m _ => ?_
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hle⟩
    exact ⟨i, by simpa using hle i⟩
  · rintro ⟨i, hi⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    intro j
    by_cases h : j = i
    · subst h; simpa using hi
    · simp [Ne.symm h]

end BallotBound

end
