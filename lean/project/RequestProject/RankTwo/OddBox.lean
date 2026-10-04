module

public import RequestProject.RankTwo.Update
public import RequestProject.RankTwo.Homog
public import RequestProject.RankTwo.TopCoeff
public import RequestProject.RankTwo.Key

/-!
# Part S of `q_rank_two.md`: (S4) and (S5)

**(S4)**: (i) is (R4), second form, with `a := −ζ^h·H(y)`, `E := Ev(y)`, `O := Od(y)`, and (S2);
(ii) is (R2) for the list `(c, Ev(y))`, its last border and `λ := −Od(y)`, and (S2).

**(S5)**: from (S4), (R3) and (R5), with (S1). The two cases of (a) (`t + 1 ≤ h` and `h ≤ t`)
and of (b) (`t ≤ h` and `h < t`) are stated together with an `if … then … else`, and then
separately. A list `c` of border columns over `A` is read over `A[ζ]` as
`fun k i => C (c k i)`.
-/

@[expose] public section

namespace RankTwo

open Finset Pfaffian Polynomial

variable {A : Type*} [CommRing A]

/-- Auxiliary for (S4) of `q_rank_two.md`: `t·a` is alternating if `a` is. -/
theorem smul_isAlt {R : Type*} [CommRing R] {n : ℕ} {a : Matrix (Fin n) (Fin n) R}
    (ha : IsAlt a) (t : R) : IsAlt (t • a) :=
  ⟨fun i => by simp [ha.1], fun i j => by simp [ha.2 i j]⟩

/-- **(S4)** (i) of Theorem S in `q_rank_two.md`: for every `y : Fin n → A` and every list `c` of
`s` border columns over `A[ζ]`,
`bpf(L(y); c) = bpf(−ζ^h·H(y); c) − bpf(−ζ^h·H(y); c, Ev(y), Od(y))`. -/
theorem S4_i (h : ℕ) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A[X]) :
    bpf (Lm h y) c = bpf ((-X ^ h : A[X]) • Hm h y) c -
      bpf ((-X ^ h : A[X]) • Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X])
        (Fin.snoc (α := fun _ => Fin n → A[X]) c (Ev h y)) (Od h y)) := by
  have e : Lm h y = (-X ^ h : A[X]) • Hm h y +
      Matrix.of fun i j => Ev h y i * Od h y j - Ev h y j * Od h y i := by
    refine funext fun i => funext fun j => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination S2 h y i j
  rw [e]
  exact R4' _ (smul_isAlt (Hm_isAlt h y) _) c _ _

/-- **(S4)** (ii) of Theorem S in `q_rank_two.md`: for every `y : Fin n → A` and every list `c`
of `s` border columns over `A[ζ]`, `bpf(L(y); c, Ev(y)) = bpf(−ζ^h·H(y); c, Ev(y))`. -/
theorem S4_ii (h : ℕ) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A[X]) :
    bpf (Lm h y) (Fin.snoc (α := fun _ => Fin n → A[X]) c (Ev h y)) =
      bpf ((-X ^ h : A[X]) • Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X]) c (Ev h y)) := by
  have h2 := (R2 ((-X ^ h : A[X]) • Hm h y) (smul_isAlt (Hm_isAlt h y) _)
    (Fin.snoc (α := fun _ => Fin n → A[X]) c (Ev h y)) (Fin.last s) (fun i => -Od h y i)).2
  rw [← h2]
  congr 1
  refine funext fun i => funext fun j => ?_
  simp only [Fin.snoc_last, Matrix.smul_apply, smul_eq_mul]
  linear_combination S2 h y i j

/-- Auxiliary for (S5) of `q_rank_two.md`: `[ζ^N] ((−ζ^h)^k·Q) = (−1)^k·[ζ^{N−hk}] Q` if
`hk ≤ N`, and `0` otherwise. -/
theorem coeff_negXpow_mul (h k N : ℕ) (Q : A[X]) :
    ((-X ^ h : A[X]) ^ k * Q).coeff N =
      (-1) ^ k * (if h * k ≤ N then Q.coeff (N - h * k) else 0) := by
  rw [neg_pow, ← pow_mul, show (-1 : A[X]) ^ k = C ((-1) ^ k) by simp, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul']

/-- **(S5)** of Theorem S in `q_rank_two.md`, (a), both cases together: for `h ≥ 1`,
`y : Fin n → A` and a list `c` of `s` border columns over `A` with `n = s + 2(t + 1)`,
`Pf(y; c) = (−1)^{t+1}·[ζ^{h−1−t}] bpf(H(y); c, Ev(y), Od(y))` if `t + 1 ≤ h`, and
`Pf(y; c) = 0` otherwise. Here `Pf(y; c) = Pfaffian.Pf (2h+1) y c` and `c` is read over `A[ζ]`
as `fun k i => C (c k i)`. -/
theorem S5a {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 2 * (t + 1))
    (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y c =
      if t + 1 ≤ h then
        (-1) ^ (t + 1) * (bpf (Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X])
          (Fin.snoc (α := fun _ => Fin n → A[X]) (fun k i => C (c k i)) (Ev h y))
            (Od h y))).coeff (h - 1 - t)
      else 0 := by
  have h5 := (R5_bpf (t + 1) (h - 1) hn (Lm h y) (Lm_isAlt h y) (fun k i => C (c k i))
    (fun _ => 0) (natDegree_Lm h y) (fun k i => by simp)).2
  simp only [Finset.sum_const_zero, add_zero, coeff_C_zero] at h5
  rw [S1_top hh] at h5
  unfold Pf
  rw [← h5, S4_i, R3_bpf (t + 1) hn _ _ (Hm_isAlt h y),
    R3_bpf t (by omega) _ _ (Hm_isAlt h y), coeff_sub, coeff_negXpow_mul, coeff_negXpow_mul]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have e1 : (h' + 1) * (t + 1) = t * h' + h' + t + 1 := by ring
  have e2 : (t + 1) * (h' + 1 - 1) = t * h' + h' := by rw [Nat.add_sub_cancel]; ring
  have e3 : (h' + 1) * t = t * h' + t := by ring
  rw [e1, e2, e3]
  generalize t * h' = P
  rw [if_neg (by omega), mul_zero, zero_sub]
  by_cases ht : t + 1 ≤ h' + 1
  · rw [if_pos (by omega), if_pos ht, show P + h' - (P + t) = h' + 1 - 1 - t by omega, pow_succ]
    ring
  · rw [if_neg (by omega), if_neg ht]
    ring

/-- **(S5)** (a) of Theorem S in `q_rank_two.md`, case `t ≤ h − 1`: if `n = s + 2(t + 1)`,
`Pf(y; c) = (−1)^{t+1}·[ζ^{h−1−t}] bpf(H(y); c, Ev(y), Od(y))`. -/
theorem S5a_of_le {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 2 * (t + 1))
    (ht : t + 1 ≤ h) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y c =
      (-1) ^ (t + 1) * (bpf (Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X])
        (Fin.snoc (α := fun _ => Fin n → A[X]) (fun k i => C (c k i)) (Ev h y))
          (Od h y))).coeff (h - 1 - t) := by
  rw [S5a hh t hn, if_pos ht]

/-- **(S5)** (a) of Theorem S in `q_rank_two.md`, case `t ≥ h`: if `n = s + 2(t + 1)`,
`Pf(y; c) = 0`. -/
theorem S5a_of_ge {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 2 * (t + 1))
    (ht : h ≤ t) (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y c = 0 := by
  rw [S5a hh t hn, if_neg (by omega)]

/-- **(S5)** of Theorem S in `q_rank_two.md`, (b), both cases together: for `h ≥ 1`,
`y : Fin n → A` and a list `c` of `s` border columns over `A` with `n = s + 1 + 2t`,
`Pf(y; c, y^{r−1}) = (−1)^t·[ζ^{h−t}] bpf(H(y); c, Ev(y))` if `t ≤ h`, and
`Pf(y; c, y^{r−1}) = 0` otherwise, where `r − 1 = 2h` and `y^{r−1}` is the column
`i ↦ y_i^{2h}`, appended as the last border. -/
theorem S5b {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 1 + 2 * t)
    (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y (Fin.snoc (α := fun _ => Fin n → A) c (fun i => y i ^ (2 * h))) =
      if t ≤ h then
        (-1) ^ t * (bpf (Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X])
          (fun k i => C (c k i)) (Ev h y))).coeff (h - t)
      else 0 := by
  set cE : Fin (s + 1) → Fin n → A[X] :=
    Fin.snoc (α := fun _ => Fin n → A[X]) (fun k i => C (c k i)) (Ev h y) with hcE
  set dk : Fin (s + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) (fun _ => 0) h with hdk
  have hdeg : ∀ k i, (cE k i).natDegree ≤ dk k := by
    intro k i
    induction k using Fin.lastCases with
    | last => simp only [hcE, hdk, Fin.snoc_last]; exact (Ev_top h y i).1
    | cast k => simp [hcE, hdk]
  have h5 := (R5_bpf t (h - 1) hn (Lm h y) (Lm_isAlt h y) cE dk (natDegree_Lm h y) hdeg).2
  have hsum : ∑ k, dk k = h := by simp [hdk, Fin.sum_univ_castSucc]
  have htop : (fun k i => (cE k i).coeff (dk k)) =
      Fin.snoc (α := fun _ => Fin n → A) c (fun i => y i ^ (2 * h)) := by
    funext k i
    induction k using Fin.lastCases with
    | last => simp only [hcE, hdk, Fin.snoc_last]; exact (Ev_top h y i).2
    | cast k => simp [hcE, hdk]
  rw [hsum, S1_top hh, htop] at h5
  unfold Pf
  rw [← h5, S4_ii, R3_bpf t (by omega) _ _ (Hm_isAlt h y), coeff_negXpow_mul]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have e2 : t * (h' + 1 - 1) = t * h' := by rw [Nat.add_sub_cancel]
  have e3 : (h' + 1) * t = t * h' + t := by ring
  rw [e2, e3]
  generalize t * h' = P
  by_cases ht : t ≤ h' + 1
  · rw [if_pos (by omega), if_pos ht, show P + (h' + 1) - (P + t) = h' + 1 - t by omega]
  · rw [if_neg (by omega), if_neg ht, mul_zero]

/-- **(S5)** (b) of Theorem S in `q_rank_two.md`, case `t ≤ h`: if `n = s + 1 + 2t`,
`Pf(y; c, y^{r−1}) = (−1)^t·[ζ^{h−t}] bpf(H(y); c, Ev(y))`. -/
theorem S5b_of_le {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 1 + 2 * t) (ht : t ≤ h)
    (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y (Fin.snoc (α := fun _ => Fin n → A) c (fun i => y i ^ (2 * h))) =
      (-1) ^ t * (bpf (Hm h y) (Fin.snoc (α := fun _ => Fin n → A[X])
        (fun k i => C (c k i)) (Ev h y))).coeff (h - t) := by
  rw [S5b hh t hn, if_pos ht]

/-- **(S5)** (b) of Theorem S in `q_rank_two.md`, case `t > h`: if `n = s + 1 + 2t`,
`Pf(y; c, y^{r−1}) = 0`. -/
theorem S5b_of_gt {h : ℕ} (hh : 1 ≤ h) {n s : ℕ} (t : ℕ) (hn : n = s + 1 + 2 * t) (ht : h < t)
    (y : Fin n → A) (c : Fin s → Fin n → A) :
    Pf (2 * h + 1) y (Fin.snoc (α := fun _ => Fin n → A) c (fun i => y i ^ (2 * h))) = 0 := by
  rw [S5b hh t hn, if_neg (by omega)]

end RankTwo
