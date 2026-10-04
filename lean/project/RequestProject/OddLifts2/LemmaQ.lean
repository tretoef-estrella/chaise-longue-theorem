module

public import RequestProject.OddLifts.Main

/-!
# Part Q of `q_oddbox_lifts_2.md`: the marked Pfaffian with one new variable, any block size

For a commutative ring `R`, natural numbers `h`, `l`, `n` and `w : Fin n → R`, put
`z := Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]`.  This file proves **Lemma Q**
(Q1), (Q2) and **Lemma Q′** (Q′1), (Q′2) of `q_oddbox_lifts_2.md`.
-/

@[expose] public section

open Polynomial Pfaffian ColOne

namespace OddLifts2

variable {R : Type*} [CommRing R]

/-- Auxiliary for **Lemma Q** and **Lemma Q′** of `q_oddbox_lifts_2.md` ((F4) of the paper,
`s + 1` borders): the expansion of `Pf_e(z)`, `z = (X, C w_1, …, C w_n)`, along the new variable
`0` (`Pfaffian.bpf_expand_var` at `x = 0`):
`Pf_e(z) = (−1)^{n+s} Pf(w; w^{e}, D^−(X, ·)) + Σ_j (−1)^{n+j} X^{e_j} Pf_{e ∖ e_j}(w)`. -/
theorem Pfe_cons_expand (h : ℕ) {n s : ℕ} (w : Fin n → R) (e : Fin (s + 1) → ℕ) :
    Pfe (2 * h + 1) (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]) e =
      (-1) ^ (n + s) * Pf (2 * h + 1) (fun i => C (w i))
        (Fin.snoc (α := fun _ => Fin n → R[X]) (fun k i => C (w i) ^ e k)
          (fun i => Dab (2 * h + 1) X (C (w i)))) +
      ∑ j : Fin (s + 1), (-1) ^ (n + (j : ℕ)) * X ^ e j *
        C (Pfe (2 * h + 1) w (fun i => e (j.succAbove i))) := by
  have hr := OddPatterns.odd_two_mul_add_one h
  have hmap : ∀ {t : ℕ} (e' : Fin t → ℕ),
      Pfe (2 * h + 1) (fun i => C (w i)) e' = C (Pfe (2 * h + 1) w e') := fun e' =>
    (OddLifts.map_Pfe (C : R →+* R[X]) _ w e').symm
  unfold Pfe Pf
  rw [bpf_expand_var _ (ay_isAlt hr _) _ 0]
  simp only [Fin.succAbove_zero, Fin.val_zero, zero_add]
  congr 1
  · rw [show n + 1 + (s + 1) = n + s + 2 by omega, pow_add, neg_one_sq, mul_one]
    congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have := hmap (fun i => e (j.succAbove i))
    unfold Pfe Pf at this
    rw [← this, show n + 1 + (j : ℕ) + 1 = n + (j : ℕ) + 2 by omega, pow_add, neg_one_sq, mul_one]
    rfl

/-- Auxiliary for **Lemma Q′** of `q_oddbox_lifts_2.md` ((F4) of the paper, no border):
`Pf_∅(z) = (−1)^{n+1} Pf(w; D^−(X, ·))` (`Pfaffian.bpf_expand_var_zero` at `x = 0`). -/
theorem Pfe_cons_expand_zero (h : ℕ) {n : ℕ} (w : Fin n → R) (e : Fin 0 → ℕ) :
    Pfe (2 * h + 1) (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]) e =
      (-1) ^ (n + 1) * Pf (2 * h + 1) (fun i => C (w i))
        (Fin.snoc (α := fun _ => Fin n → R[X]) (fun k i => C (w i) ^ e k)
          (fun i => Dab (2 * h + 1) X (C (w i)))) := by
  have hr := OddPatterns.odd_two_mul_add_one h
  unfold Pfe Pf
  rw [bpf_expand_var_zero _ (ay_isAlt hr _) _ 0]
  simp only [Fin.succAbove_zero, Fin.val_zero, zero_add, add_zero]
  congr 2

/-- Auxiliary for **Lemma Q** and **Lemma Q′** of `q_oddbox_lifts_2.md`: the Pfaffian of the
constants `C w` with the borders `(C w)^{e_k}` and a last border `(C w)^u` is the constant
`C (Pf_{(e, u)}(w))`. -/
theorem Pf_C_snoc_pow (h : ℕ) {n s : ℕ} (w : Fin n → R) (e : Fin s → ℕ) (u : ℕ) :
    Pf (2 * h + 1) (fun i => C (w i))
        (Fin.snoc (α := fun _ => Fin n → R[X]) (fun k i => C (w i) ^ e k) (fun b => C (w b) ^ u)) =
      C (Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) e u)) := by
  rw [OddLifts.map_Pfe (C : R →+* R[X])]
  unfold Pfe
  congr 1
  funext k i
  refine Fin.lastCases ?_ (fun j => ?_) k <;> simp

/-- Auxiliary for **Lemma Q** of `q_oddbox_lifts_2.md`: the coefficients of the first term of (F4)
after (C1) `Pfaffian.C1`:
`[X^k] Pf(C w; (C w)^{e}, D^−(X, ·)) = −Σ_{u < 2h} [k = 2h − 1 − u] (−1)^u Pf_{(e, u)}(w)`. -/
theorem coeff_Pf_Dminus (h : ℕ) {n s : ℕ} (w : Fin n → R) (e : Fin s → ℕ) (k : ℕ) :
    (Pf (2 * h + 1) (fun i => C (w i))
        (Fin.snoc (α := fun _ => Fin n → R[X]) (fun k i => C (w i) ^ e k)
          (fun i => Dab (2 * h + 1) X (C (w i))))).coeff k =
      -∑ u ∈ Finset.range (2 * h), (if k = 2 * h - 1 - u then
        (-1) ^ u * Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) e u) else 0) := by
  rw [C1 (OddPatterns.odd_two_mul_add_one h)]
  simp only [Pf_C_snoc_pow, coeff_neg, finset_sum_coeff, OddLifts.coeff_sign_X_pow_C]
  rw [show 2 * h + 1 - 1 = 2 * h by omega]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun u _ => ?_))
  rw [show 2 * h + 1 - 2 - u = 2 * h - 1 - u by omega]


/-- Auxiliary for **Lemma Q** and **Lemma Q′** of `q_oddbox_lifts_2.md`: for `L ≥ 1`,
`mPf_L(z) = Pf_{(0, …, L−2)}(z)`. -/
theorem mPf_succ_eq (h s : ℕ) {n : ℕ} {A : Type*} [CommRing A] (z : Fin n → A) :
    OddPatterns.mPf h (s + 1) z = Pfe (2 * h + 1) z (fun k : Fin s => (k : ℕ)) := by
  simp only [OddPatterns.mPf, if_neg (Nat.succ_ne_zero s)]
  rfl

/-- Auxiliary for **Lemma Q** of `q_oddbox_lifts_2.md`: `mPf_0(z) = Pf_{(2h)}(z)`. -/
theorem mPf_zero_eq (h : ℕ) {n : ℕ} {A : Type*} [CommRing A] (z : Fin n → A) :
    OddPatterns.mPf h 0 z = Pfe (2 * h + 1) z (fun _ : Fin 1 => 2 * h) := by
  simp only [OddPatterns.mPf, if_pos]

/-- Auxiliary for **Lemma Q** of `q_oddbox_lifts_2.md`: the coefficients of `Pf_e(z)` (`s + 1`
borders), read off from `Pfe_cons_expand` and `coeff_Pf_Dminus`. -/
theorem coeff_Pfe_cons (h : ℕ) {n s : ℕ} (w : Fin n → R) (e : Fin (s + 1) → ℕ) (k : ℕ) :
    (Pfe (2 * h + 1) (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]) e).coeff k =
      (-1) ^ (n + s) * -∑ u ∈ Finset.range (2 * h), (if k = 2 * h - 1 - u then
        (-1) ^ u * Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) e u) else 0) +
      ∑ j : Fin (s + 1), (if k = e j then
        (-1) ^ (n + (j : ℕ)) * Pfe (2 * h + 1) w (fun i => e (j.succAbove i)) else 0) := by
  rw [Pfe_cons_expand, coeff_add, show (-1 : R[X]) ^ (n + s) = C ((-1) ^ (n + s)) by simp,
    coeff_C_mul, coeff_Pf_Dminus]
  simp only [finset_sum_coeff, OddLifts.coeff_sign_X_pow_C]

/-- Auxiliary for **Lemma Q** of `q_oddbox_lifts_2.md`: the coefficients of `Pf_∅(z)`. -/
theorem coeff_Pfe_cons_zero (h : ℕ) {n : ℕ} (w : Fin n → R) (e : Fin 0 → ℕ) (k : ℕ) :
    (Pfe (2 * h + 1) (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X]) e).coeff k =
      (-1) ^ (n + 1) * -∑ u ∈ Finset.range (2 * h), (if k = 2 * h - 1 - u then
        (-1) ^ u * Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) e u) else 0) := by
  rw [Pfe_cons_expand_zero, show (-1 : R[X]) ^ (n + 1) = C ((-1) ^ (n + 1)) by simp,
    coeff_C_mul, coeff_Pf_Dminus]

/-- Auxiliary for **Lemma Q** of `q_oddbox_lifts_2.md`: the borders `(0, …, s, s+1)` are
`(0, …, s+1)`. -/
theorem snoc_range_eq (s : ℕ) :
    (Fin.snoc (α := fun _ => ℕ) (fun k : Fin s => (k : ℕ)) s) = fun k : Fin (s + 1) => (k : ℕ) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k <;> simp

/-- **Lemma Q, (Q1)** of `q_oddbox_lifts_2.md`: let `n = l + 2 + 2t` and `l + 1 ≤ h`; for
`w : Fin n → R` and `z = Fin.cons X (fun i => C (w i))`, `[X^k] mPf_l(z) = 0` for every `k` with
`2h − l < k`.  (The hypothesis `n = l + 2 + 2t` is kept as stated in the source, but the proof of
(Q1) does not use it: (Q1) holds for every `n`.) -/
theorem Q1 {R : Type*} [CommRing R] (h l n t : ℕ) (hn : n = l + 2 + 2 * t) (hlh : l + 1 ≤ h)
    (w : Fin n → R) (k : ℕ) (hk : 2 * h - l < k) :
    (OddPatterns.mPf h l (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X])).coeff k = 0 := by
  rcases l with _ | _ | s
  · rw [mPf_zero_eq, coeff_Pfe_cons (s := 0)]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, neg_zero, mul_zero, add_zero]
    · intro j _; rw [if_neg (by omega)]
    · intro u hu; rw [Finset.mem_range] at hu; rw [if_neg (by omega)]
  · rw [mPf_succ_eq, coeff_Pfe_cons_zero]
    rw [Finset.sum_eq_zero, neg_zero, mul_zero]
    intro u hu; rw [Finset.mem_range] at hu; rw [if_neg (by omega)]
  · rw [mPf_succ_eq, coeff_Pfe_cons]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, neg_zero, mul_zero, add_zero]
    · intro j _
      have := j.isLt
      rw [if_neg (by omega)]
    · intro u hu
      rw [Finset.mem_range] at hu
      split_ifs with hm
      · rw [OddLifts.Pfe_snoc_eq_zero h s w (by omega), mul_zero]
      · rfl

/-- **Lemma Q, (Q2)** of `q_oddbox_lifts_2.md`: let `n = l + 2 + 2t` and `l + 1 ≤ h`; for
`w : Fin n → R` and `z = Fin.cons X (fun i => C (w i))`,
`[X^{2h−l}] mPf_l(z) = (−1)^l · mPf_{l+1}(w)`. -/
theorem Q2 {R : Type*} [CommRing R] (h l n t : ℕ) (hn : n = l + 2 + 2 * t) (hlh : l + 1 ≤ h)
    (w : Fin n → R) :
    (OddPatterns.mPf h l (Fin.cons X (fun i => C (w i)) : Fin (n + 1) → R[X])).coeff (2 * h - l) =
      (-1) ^ l * OddPatterns.mPf h (l + 1) w := by
  rcases l with _ | _ | s
  · rw [mPf_zero_eq, coeff_Pfe_cons (s := 0), mPf_succ_eq]
    rw [Finset.sum_eq_zero, neg_zero, mul_zero, zero_add, Fin.sum_univ_one, if_pos (by simp)]
    · simp only [Fin.val_zero, add_zero, pow_zero, one_mul]
      rw [Even.neg_one_pow ⟨t + 1, by omega⟩, one_mul]
      congr 1
      funext i
      exact Fin.elim0 i
    · intro u hu; rw [Finset.mem_range] at hu; rw [if_neg (by omega)]
  · rw [mPf_succ_eq, coeff_Pfe_cons_zero, mPf_succ_eq]
    rw [Finset.sum_eq_single 0]
    · rw [if_pos (by omega), show (Fin.snoc (α := fun _ => ℕ) (fun k : Fin 0 => (k : ℕ)) 0) =
        fun k : Fin 1 => (k : ℕ) from snoc_range_eq 0]
      rw [Even.neg_one_pow ⟨t + 2, by omega⟩, one_mul]
      ring
    · intro u hu hne
      rw [Finset.mem_range] at hu
      rw [if_neg (by omega)]
    · intro hn
      exact absurd (Finset.mem_range.2 (by omega)) hn
  · rw [mPf_succ_eq, coeff_Pfe_cons, mPf_succ_eq]
    rw [Finset.sum_eq_zero (s := Finset.univ), add_zero]
    swap
    · intro j _
      have := j.isLt
      rw [if_neg (by omega)]
    rw [Finset.sum_eq_single (s + 1)]
    · rw [if_pos (by omega), snoc_range_eq (s + 1)]
      rw [Even.neg_one_pow ⟨s + t + 2, by omega⟩, one_mul]
      ring
    · intro u hu hne
      rw [Finset.mem_range] at hu
      split_ifs with hm
      · rw [OddLifts.Pfe_snoc_eq_zero h s w (by omega), mul_zero]
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.2 (by omega)) hn

end OddLifts2
