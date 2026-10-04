module

public import RequestProject.OddPatterns.Main

/-!
# Part P of `q_oddbox_lifts_1.md`: the marked Pfaffian with one new variable

For a commutative ring `R`, `h ≥ 0`, `ℓ ≥ 1` and `w : Fin ℓ → R`, let
`z = Fin.cons X (fun i => C (w i)) : Fin (ℓ+1) → R[X]` and `P_ℓ(w) := mPf_ℓ(z)`
(`OddPatterns.mPf h ℓ z`).  This file proves **Lemma P** (P1)–(P3) of `q_oddbox_lifts_1.md`.
((P0) is `OddPatterns.A1`.)
-/

@[expose] public section

open Polynomial Pfaffian ColOne

namespace OddLifts

variable {A : Type*} [CommRing A]

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: the Pfaffians `Pf_e` commute
with ring homomorphisms. -/
theorem map_Pfe {A' : Type*} [CommRing A'] (f : A →+* A') (r : ℕ) {n s : ℕ} (z : Fin n → A)
    (e : Fin s → ℕ) : f (Pfe r z e) = Pfe r (fun i => f (z i)) e := by
  unfold Pfe Pf bpf
  rw [OddPatterns.map_pf]
  congr 1
  funext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j => simp [ay, map_Dab]
    | right k => simp
  | right k =>
    induction q using Fin.addCases with
    | left j => simp
    | right k' => simp

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: the expansion of the bordered
Pfaffian `mPf_{s+2}(z)` along the variable `0` (`Pfaffian.bpf_expand_var` with `x = 0`), the first
term being rewritten by (C1) `Pfaffian.C1`:
`mPf_{s+2}(z) = −Σ_{u=0}^{2h−1} (−1)^u z_0^{2h−1−u} Pf_{(0,…,s,u)}(z') +
  Σ_{k=0}^{s} (−1)^{s+k+4} z_0^k Pf_{(0,…,s) ∖ k}(z')`, with `z' = (z_1, …, z_{s+2})`. -/
theorem mPf_expand (h s : ℕ) (z : Fin (s + 3) → A) :
    OddPatterns.mPf h (s + 2) z =
      -∑ u ∈ Finset.range (2 * h), (-1) ^ u * z 0 ^ (2 * h - 1 - u) *
          Pfe (2 * h + 1) (fun i => z i.succ)
            (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) u) +
        ∑ k : Fin (s + 1), (-1) ^ (s + 3 + (k : ℕ) + 1) * z 0 ^ (k : ℕ) *
          Pfe (2 * h + 1) (fun i => z i.succ) (fun j : Fin s => ((k.succAbove j : Fin (s + 1)) : ℕ)) := by
  have hr := OddPatterns.odd_two_mul_add_one h
  simp only [OddPatterns.mPf, if_neg (show s + 2 ≠ 0 by omega)]
  show bpf (ay (2 * h + 1) z) (fun (k : Fin (s + 1)) i => z i ^ (k : ℕ)) = _
  rw [bpf_expand_var _ (ay_isAlt hr z) _ 0]
  simp only [Fin.succAbove_zero, Fin.val_zero]
  congr 1
  · have e1 : (ay (2 * h + 1) z).submatrix Fin.succ Fin.succ = ay (2 * h + 1) (fun i => z i.succ) :=
      rfl
    have e2 : (fun i : Fin (s + 2) => ay (2 * h + 1) z 0 i.succ) =
        fun b => Dab (2 * h + 1) (z 0) (z b.succ) := rfl
    have hC := C1 hr (fun i => z i.succ) (fun (k : Fin (s + 1)) i => z i.succ ^ (k : ℕ)) (z 0)
    unfold Pf at hC
    rw [e1, e2, hC]
    have e3 : ∀ u : ℕ, (Fin.snoc (α := fun _ => Fin (s + 2) → A)
        (fun (k : Fin (s + 1)) i => z i.succ ^ (k : ℕ)) (fun b => z b.succ ^ u)) =
        fun k i => z i.succ ^ (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) u k) := by
      intro u
      funext k i
      refine Fin.lastCases ?_ (fun j => ?_) k <;> simp
    simp only [e3]
    rw [show (0 : ℕ) + (s + 2 + 1) + (s + 1) = 2 * (s + 2) by ring, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, Pfe, Pf]
    rw [show 2 * h + 1 - 1 = 2 * h by omega]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun u _ => ?_)
    rw [show 2 * h + 1 - 2 - u = 2 * h - 1 - u by omega]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show 0 + (s + 2 + 1) + (k : ℕ) + 1 = s + 3 + k + 1 by omega]
    rfl

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: the coefficients of a
monomial `±X^j · C a`. -/
theorem coeff_sign_X_pow_C (u j m : ℕ) (a : A) :
    ((-1 : A[X]) ^ u * X ^ j * C a).coeff m = if m = j then (-1) ^ u * a else 0 := by
  rw [show (-1 : A[X]) ^ u * X ^ j * C a = C ((-1) ^ u * a) * X ^ j by simp only [map_mul, map_pow, map_neg, map_one]; ring,
    coeff_C_mul_X_pow]

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: the Pfaffian
`Pf(w; w^0, …, w^s, w^u)` with two equal borders vanishes for `u ≤ s`
(`Pfaffian.bpf_eq_zero_of_border_eq`). -/
theorem Pfe_snoc_eq_zero (h s : ℕ) {n : ℕ} (w : Fin n → A) {u : ℕ} (hu : u ≤ s) :
    Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) u) = 0 := by
  unfold Pfe Pf
  refine bpf_eq_zero_of_border_eq _ (ay_isAlt (OddPatterns.odd_two_mul_add_one h) w) _
    (k := (⟨u, by omega⟩ : Fin (s + 1)).castSucc) (k' := Fin.last (s + 1))
    (Fin.castSucc_lt_last _).ne ?_
  funext i
  rw [Fin.snoc_castSucc, Fin.snoc_last]

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: for `u = s + 1` the borders
are `w^0, …, w^{s+1}`, and (C5) `Pfaffian.C5` gives
`Pf_{(0,…,s+1)}(w) = (−1)^{(s+2)(s+1)/2} Π_{i<j} (w_j − w_i)`. -/
theorem Pfe_snoc_top (h s : ℕ) (w : Fin (s + 2) → A) :
    Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) (s + 1)) =
      (-1) ^ ((s + 2) * (s + 2 - 1) / 2) * ∏ i : Fin (s + 2), ∏ j ∈ Finset.Ioi i, (w j - w i) := by
  have e : (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) (s + 1)) =
      fun k : Fin (s + 2) => (k : ℕ) := by
    funext k
    refine Fin.lastCases ?_ (fun j => ?_) k <;> simp
  rw [e]
  exact C5 (OddPatterns.odd_two_mul_add_one h) w

/-- Auxiliary for the proof of **Lemma P** of `q_oddbox_lifts_1.md`: the coefficients of
`P_{s+2}(w)`, read off from `mPf_expand`. -/
theorem coeff_mPf_cons (h s : ℕ) (w : Fin (s + 2) → A) (m : ℕ) :
    (OddPatterns.mPf h (s + 2) (Fin.cons X (fun i => C (w i)) : Fin (s + 3) → A[X])).coeff m =
      -∑ u ∈ Finset.range (2 * h), (if m = 2 * h - 1 - u then (-1) ^ u *
          Pfe (2 * h + 1) w (Fin.snoc (α := fun _ => ℕ) (fun k : Fin (s + 1) => (k : ℕ)) u)
          else 0) +
        ∑ k : Fin (s + 1), (if m = (k : ℕ) then (-1) ^ (s + 3 + (k : ℕ) + 1) *
          Pfe (2 * h + 1) w (fun j : Fin s => ((k.succAbove j : Fin (s + 1)) : ℕ)) else 0) := by
  rw [mPf_expand]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hmap : ∀ {t : ℕ} (e : Fin t → ℕ),
      Pfe (2 * h + 1) (fun i => C (w i)) e = C (Pfe (2 * h + 1) w e) := fun e =>
    (map_Pfe (C : A →+* A[X]) _ w e).symm
  simp only [hmap, coeff_add, coeff_neg, finset_sum_coeff, coeff_sign_X_pow_C]

/-- **Lemma P, (P1)** of `q_oddbox_lifts_1.md`: for `ℓ ≥ 1`, `w : Fin ℓ → R` and
`z = Fin.cons X (fun i => C (w i))`, the coefficient `[X^k] P_ℓ(w)` of `P_ℓ(w) = mPf_ℓ(z)`
vanishes for every `k` with `2h < k + ℓ` and `ℓ < k + 2`. -/
theorem P1 {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (k : ℕ)
    (hk1 : 2 * h < k + l) (hk2 : l < k + 2) :
    (OddPatterns.mPf h l (Fin.cons X (fun i => C (w i)) : Fin (l + 1) → R[X])).coeff k = 0 := by
  rcases l with _ | _ | s
  · omega
  · rw [OddPatterns.A2]
    simp only [Fin.cons_zero, Fin.cons_one, Dab, finset_sum_coeff]
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [show (-1 : R[X]) ^ u * X ^ u * C (w 0) ^ (2 * h + 1 - 2 - u) =
      C ((-1) ^ u * w 0 ^ (2 * h + 1 - 2 - u)) * X ^ u by simp only [map_mul, map_pow, map_neg, map_one]; ring, coeff_C_mul_X_pow,
      if_neg (by omega)]
  · rw [coeff_mPf_cons]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, neg_zero, add_zero]
    · intro j _
      rw [if_neg (by omega)]
    · intro u hu
      rw [Finset.mem_range] at hu
      split_ifs with hm
      · rw [Pfe_snoc_eq_zero h s w (by omega), mul_zero]
      · rfl

/-- **Lemma P, (P2)** of `q_oddbox_lifts_1.md`: if `1 ≤ ℓ ≤ h`, then
`[X^{2h−ℓ}] P_ℓ(w) = (−1)^{ℓ(ℓ+1)/2} · Π_{i<j} (w_j − w_i)` (the product over `i < j` in
`Fin ℓ`). -/
theorem P2 {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (hlh : l ≤ h) :
    (OddPatterns.mPf h l (Fin.cons X (fun i => C (w i)) : Fin (l + 1) → R[X])).coeff (2 * h - l) =
      (-1) ^ (l * (l + 1) / 2) * ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, (w j - w i) := by
  rcases l with _ | _ | s
  · omega
  · rw [OddPatterns.A2]
    simp only [Fin.cons_zero, Fin.cons_one, Dab, finset_sum_coeff]
    rw [Finset.sum_eq_single (2 * h - 1)]
    · rw [show (-1 : R[X]) ^ (2 * h - 1) * X ^ (2 * h - 1) * C (w 0) ^ (2 * h + 1 - 2 - (2 * h - 1)) =
        C ((-1) ^ (2 * h - 1) * w 0 ^ (2 * h + 1 - 2 - (2 * h - 1))) * X ^ (2 * h - 1) by simp only [map_mul, map_pow, map_neg, map_one]; ring,
        coeff_C_mul_X_pow, if_pos (by omega), show 2 * h + 1 - 2 - (2 * h - 1) = 0 by omega]
      have hI : ∀ i : Fin (0 + 1), Finset.Ioi i = ∅ := fun i =>
        Finset.eq_empty_of_forall_notMem (fun j hj => by
          have h1 := Finset.mem_Ioi.1 hj
          rw [Fin.lt_def] at h1
          have := j.isLt
          omega)
      simp only [pow_zero, mul_one, hI, Finset.prod_empty, Finset.prod_const_one]
      rw [show 2 * h - 1 = 2 * (h - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num
    · intro u hu hne
      rw [show (-1 : R[X]) ^ u * X ^ u * C (w 0) ^ (2 * h + 1 - 2 - u) =
        C ((-1) ^ u * w 0 ^ (2 * h + 1 - 2 - u)) * X ^ u by simp only [map_mul, map_pow, map_neg, map_one]; ring, coeff_C_mul_X_pow,
        if_neg (by omega)]
    · intro hn
      exact absurd (Finset.mem_range.2 (by omega)) hn
  · rw [coeff_mPf_cons]
    rw [Finset.sum_eq_zero (s := Finset.univ), add_zero]
    swap
    · intro j _
      rw [if_neg (by omega)]
    rw [Finset.sum_eq_single (s + 1)]
    · rw [if_pos (by omega), Pfe_snoc_top]
      have e : (s + 1 + 1) * (s + 1 + 1 + 1) / 2 = (s + 2) * (s + 2 - 1) / 2 + (s + 2) := by
        rw [show (s + 1 + 1) * (s + 1 + 1 + 1) = (s + 2) * (s + 2 - 1) + 2 * (s + 2) by
          rw [show s + 2 - 1 = s + 1 by omega]; ring, Nat.add_mul_div_left _ _ (by norm_num)]
      rw [e, pow_add (-1 : R) ((s + 2) * (s + 2 - 1) / 2) (s + 2)]
      ring
    · intro u hu hne
      rw [Finset.mem_range] at hu
      split_ifs with hm
      · omega
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.2 (by omega)) hn

/-- **Lemma P, (P3)** of `q_oddbox_lifts_1.md`: if `1 ≤ ℓ ≤ h`, then `[X^k] P_ℓ(w) = 0` for every
`k > 2h − ℓ` (a consequence of (P1)). -/
theorem P3 {R : Type*} [CommRing R] (h l : ℕ) (hl : 1 ≤ l) (w : Fin l → R) (hlh : l ≤ h) (k : ℕ)
    (hk : 2 * h - l < k) :
    (OddPatterns.mPf h l (Fin.cons X (fun i => C (w i)) : Fin (l + 1) → R[X])).coeff k = 0 :=
  P1 h l hl w k (by omega) (by omega)

end OddLifts
