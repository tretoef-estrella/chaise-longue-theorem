module

public import RequestProject.OddLifts2.LemmaQ

/-!
# Part Q of `q_oddbox_lifts_2.md`: Lemma Q′

For a commutative ring `R`, natural numbers `h`, `ℓ`, `n` and `w : Fin n → R`, with
`z := Fin.cons X (fun i => C (w i))`,
`Φ := X · mPf_{ℓ+1}(z) + Pf(C w; (C w)^0, …, (C w)^{ℓ−1}, D(X, ·))` (`D = ColOne.Dab (2h+2)`).
This file proves **Lemma Q′** (Q′1), (Q′2) of `q_oddbox_lifts_2.md`.
-/

@[expose] public section

open Polynomial Pfaffian ColOne

namespace OddLifts2

variable {R : Type*} [CommRing R]

/-- **Lemma Q′** of `q_oddbox_lifts_2.md`, the polynomial
`Φ := X · mPf h (ℓ+1) z + Pf (2h+1) (C w) ((C w)^0, …, (C w)^{ℓ−1}, D(X, ·))`, where
`z = Fin.cons X (fun i => C (w i))` and `D = ColOne.Dab (2h+2)`. -/
noncomputable def Phi (h ell : ℕ) {n : ℕ} (w : Fin n → R) : R[X] :=
  X * OddPatterns.mPf h (ell + 1) (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]) +
    Pf (2 * h + 1) (fun i => C (w i))
      (Fin.snoc (α := fun _ => Fin n → R[X]) (fun (k : Fin ell) i => (C (w i)) ^ (k : ℕ))
        (fun b => Dab (2 * h + 2) X (C (w b))))

/-- Auxiliary for **Lemma Q′** of `q_oddbox_lifts_2.md`: (C3) `Pfaffian.C3` for the last border
`D(X, ·)` of `Φ`: `Pf(C w; c, D(X, ·)) = C(Pf_{(e, 2h)}(w)) − X · Pf(C w; c, D^−(X, ·))`. -/
theorem Pf_D_eq (h : ℕ) {n ell : ℕ} (w : Fin n → R) :
    Pf (2 * h + 1) (fun i => C (w i))
      (Fin.snoc (α := fun _ => Fin n → R[X]) (fun (k : Fin ell) i => (C (w i)) ^ (k : ℕ))
        (fun b => Dab (2 * h + 2) X (C (w b)))) =
      C (Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) (fun k : Fin ell => (k : ℕ)) (2 * h))) -
        X * Pf (2 * h + 1) (fun i => C (w i))
          (Fin.snoc (α := fun _ => Fin n → R[X]) (fun (k : Fin ell) i => (C (w i)) ^ (k : ℕ))
            (fun i => Dab (2 * h + 1) X (C (w i)))) := by
  have h3 := C3 (OddPatterns.odd_two_mul_add_one h) (fun i => C (w i))
    (fun (k : Fin ell) i => (C (w i)) ^ (k : ℕ)) X
  rw [show 2 * h + 1 + 1 = 2 * h + 2 from rfl, show 2 * h + 1 - 1 = 2 * h by omega] at h3
  rw [h3, ← Pf_C_snoc_pow h w (fun k : Fin ell => (k : ℕ)) (2 * h)]

/-- Auxiliary for **Lemma Q′** of `q_oddbox_lifts_2.md`, case `ℓ = 0`: the two terms with
`D^−(X, ·)` cancel and `Φ = Pf(w; w^{2h}) = mPf_0(w)` (a constant). -/
theorem Phi_zero (h t : ℕ) {n : ℕ} (hn : n = 0 + 1 + 2 * t) (w : Fin n → R) :
    Phi h 0 w = C (OddPatterns.mPf h 0 w) := by
  unfold Phi
  rw [Pf_D_eq, mPf_succ_eq, Pfe_cons_expand_zero, Even.neg_one_pow ⟨t + 1, by omega⟩, one_mul,
    mPf_zero_eq]
  have e : (Fin.snoc (α := fun _ => ℕ) (fun k : Fin 0 => (k : ℕ)) (2 * h)) = fun _ => 2 * h := by
    funext k
    rw [Fin.fin_one_eq_zero k]
    rfl
  rw [e]
  ring

/-- Auxiliary for **Lemma Q′** of `q_oddbox_lifts_2.md`, case `ℓ = s + 1`: the two terms with
`D^−(X, ·)` cancel and
`Φ = Σ_j (−1)^{n+j} X^{j+1} Pf_{(0,…,s) ∖ j}(w) + Pf_{(0,…,s,2h)}(w)`. -/
theorem Phi_succ (h s t : ℕ) {n : ℕ} (hn : n = s + 1 + 1 + 2 * t) (w : Fin n → R) :
    Phi h (s + 1) w =
      (∑ j : Fin (s + 1), (-1) ^ (n + (j : ℕ)) * X ^ ((j : ℕ) + 1) *
        C (Pfe (2 * h + 1) w (fun i => ((j.succAbove i : Fin (s + 1)) : ℕ)))) +
      C (Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) (2 * h))) := by
  unfold Phi
  rw [Pf_D_eq, mPf_succ_eq, Pfe_cons_expand, Even.neg_one_pow ⟨s + t + 1, by omega⟩, one_mul,
    mul_add, Finset.mul_sum]
  have e : ∀ j : Fin (s + 1), X * ((-1) ^ (n + (j : ℕ)) * X ^ (j : ℕ) *
      C (Pfe (2 * h + 1) w (fun i => ((j.succAbove i : Fin (s + 1)) : ℕ)))) =
      (-1) ^ (n + (j : ℕ)) * X ^ ((j : ℕ) + 1) *
        C (Pfe (2 * h + 1) w (fun i => ((j.succAbove i : Fin (s + 1)) : ℕ))) := fun j => by ring
  simp only [e]
  ring

/-- **Lemma Q′, (Q′1)** of `q_oddbox_lifts_2.md`: let `n = ℓ + 1 + 2t` (no hypothesis on `h`);
then `[X^k] Φ = 0` for every `k` with `ℓ < k`. -/
theorem Q'1 {R : Type*} [CommRing R] (h ell n t : ℕ) (hn : n = ell + 1 + 2 * t) (w : Fin n → R)
    (k : ℕ) (hk : ell < k) : (Phi h ell w).coeff k = 0 := by
  rcases ell with _ | s
  · rw [Phi_zero h t hn, coeff_C, if_neg (by omega)]
  · rw [Phi_succ h s t (by omega), coeff_add, coeff_C, if_neg (by omega), add_zero,
      finset_sum_coeff]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [OddLifts.coeff_sign_X_pow_C, if_neg (by have := j.isLt; omega)]

/-- **Lemma Q′, (Q′2)** of `q_oddbox_lifts_2.md`: let `n = ℓ + 1 + 2t` (no hypothesis on `h`);
then `[X^ℓ] Φ = mPf h ℓ w`. -/
theorem Q'2 {R : Type*} [CommRing R] (h ell n t : ℕ) (hn : n = ell + 1 + 2 * t) (w : Fin n → R) :
    (Phi h ell w).coeff ell = OddPatterns.mPf h ell w := by
  rcases ell with _ | s
  · rw [Phi_zero h t hn, coeff_C, if_pos rfl]
  · rw [Phi_succ h s t (by omega), coeff_add, coeff_C, if_neg (by omega), add_zero,
      finset_sum_coeff, Finset.sum_eq_single (Fin.last s)]
    · rw [OddLifts.coeff_sign_X_pow_C, if_pos (by simp), Fin.val_last,
        Even.neg_one_pow ⟨s + t + 1, by omega⟩, one_mul, mPf_succ_eq]
      congr 1
      funext i
      simp
    · intro j _ hj
      rw [OddLifts.coeff_sign_X_pow_C, if_neg]
      intro h'
      exact hj (Fin.ext (by rw [Fin.val_last]; omega))
    · intro h'
      exact absurd (Finset.mem_univ _) h'

end OddLifts2
