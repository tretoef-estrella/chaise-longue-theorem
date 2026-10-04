module

public import RequestProject.Pfaffian.Laplace
public import RequestProject.OddShapes.Identities

/-!
# Part C of `q_pfaffian.md`: the Pfaffians of the odd box

The matrix `a_y(i, j) := D^−(y_i, y_j)` with `D^− = ColOne.Dab r` (used unchanged), the
bordered Pfaffians `Pf(y; c) := bpf(a_y; c)` and `Pf_e(y)`, and Theorem C (C1)–(C6).
From `q_oddbox_shapes.md` we use, unchanged, `OddShapes.A1`, `OddShapes.A2_Dminus`,
`OddShapes.A4_D` and `OddShapes.A4_Dminus` (with `D = Dab (r+1)` and `D^− = Dab r`).

As in Part B, a list of `s` border columns is a family `c : Fin s → Fin n → A`, and a list of
exponents is `e : Fin s → ℕ`; appending a last border `v` is `Fin.snoc c v`.
-/

@[expose] public section

namespace Pfaffian

open Finset Equiv ColOne

variable {A : Type*} [CommRing A]

/-! ### Linearity in the last border (from (B2)) -/

/-- (B2) of `q_pfaffian.md` for the last border: additivity and homogeneity. -/
theorem bpf_snoc_add {n s : ℕ} (a : Matrix (Fin n) (Fin n) A) (ha : IsAlt a)
    (c : Fin s → Fin n → A) (x y : Fin n → A) (t : A) :
    bpf a (Fin.snoc (α := fun _ => Fin n → A) c (fun i => x i + t * y i)) =
      bpf a (Fin.snoc (α := fun _ => Fin n → A) c x) +
        t * bpf a (Fin.snoc (α := fun _ => Fin n → A) c y) := by
  have h := bpf_add_border a ha (Fin.snoc (α := fun _ => Fin n → A) c x) (Fin.last s) x y t
  simp only [Fin.update_snoc_last] at h
  exact h

/-- (B2) of `q_pfaffian.md` for the last border: a zero last border gives `0`. -/
theorem bpf_snoc_zero {n s : ℕ} (a : Matrix (Fin n) (Fin n) A) (ha : IsAlt a)
    (c : Fin s → Fin n → A) :
    bpf a (Fin.snoc (α := fun _ => Fin n → A) c (fun _ => 0)) = 0 := by
  have h := bpf_snoc_add a ha c (fun _ => 0) (fun _ => 0) 1
  simp only [mul_zero, add_zero, one_mul] at h
  linear_combination -h

/-- (B2) of `q_pfaffian.md` for the last border: linearity for a finite linear combination. -/
theorem bpf_snoc_sum {n s : ℕ} {ι : Type*} (a : Matrix (Fin n) (Fin n) A) (ha : IsAlt a)
    (c : Fin s → Fin n → A) (U : Finset ι) (f : ι → A) (g : ι → Fin n → A) :
    bpf a (Fin.snoc (α := fun _ => Fin n → A) c (fun i => ∑ u ∈ U, f u * g u i)) =
      ∑ u ∈ U, f u * bpf a (Fin.snoc (α := fun _ => Fin n → A) c (g u)) := by
  classical
  induction U using Finset.induction_on with
  | empty => simpa using bpf_snoc_zero a ha c
  | insert u U hu ih =>
    simp only [sum_insert hu]
    have h := bpf_snoc_add a ha c (fun i => ∑ v ∈ U, f v * g v i) (g u) (f u)
    rw [← ih, show (fun i => f u * g u i + ∑ v ∈ U, f v * g v i) =
      (fun i => ∑ v ∈ U, f v * g v i + f u * g u i) from funext fun i => add_comm _ _, h,
      add_comm]

/-! ### Definitions -/

/-- Auxiliary for Part C of `q_pfaffian.md`: `Σ_{u < 2k} (−1)^u = 0`. -/
theorem sum_neg_one_pow_even (k : ℕ) : ∑ u ∈ range (2 * k), (-1 : A) ^ u = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      pow_succ, pow_mul]
    simp

/-- **Part C** of `q_pfaffian.md`: `D^−(a, a) = 0` for odd `r` (it is
`a^{r−2}·Σ_{u=0}^{r−2} (−1)^u`, an even number of terms). -/
theorem Dab_self {r : ℕ} (hr : Odd r) (x : A) : Dab r x x = 0 := by
  obtain ⟨k, rfl⟩ := hr
  unfold Dab
  rw [show 2 * k + 1 - 1 = 2 * k by omega]
  have e : ∀ u ∈ range (2 * k), (-1 : A) ^ u * x ^ u * x ^ (2 * k + 1 - 2 - u) =
      (-1) ^ u * x ^ (2 * k - 1) := by
    intro u hu
    rw [mem_range] at hu
    rw [mul_assoc, ← pow_add, show u + (2 * k + 1 - 2 - u) = 2 * k - 1 by omega]
  rw [sum_congr rfl e, ← sum_mul, sum_neg_one_pow_even, zero_mul]

/-- **Part C** of `q_pfaffian.md`: the matrix `a_y(i, j) := D^−(y_i, y_j)` on `Fin n`, with
`D^− = ColOne.Dab r`. -/
def ay (r : ℕ) {n : ℕ} (y : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  fun i j => Dab r (y i) (y j)

/-- **Part C** of `q_pfaffian.md`: for odd `r`, the matrix `a_y` is alternating (by (A2) of
`q_oddbox_shapes.md` and `D^−(a, a) = 0`). -/
theorem ay_isAlt {r : ℕ} (hr : Odd r) {n : ℕ} (y : Fin n → A) : IsAlt (ay r y) :=
  ⟨fun i => Dab_self hr (y i), fun i j => OddShapes.A2_Dminus r hr (y i) (y j)⟩

/-- **Part C** of `q_pfaffian.md`: `Pf(y; c) := bpf(a_y; c)` for a list `c` of border columns
`Fin n → A`. -/
noncomputable def Pf (r : ℕ) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A) : A :=
  bpf (ay r y) c

/-- **Part C** of `q_pfaffian.md`: for a list of exponents `e = (e_0, …, e_{s−1})`,
`Pf_e(y) := Pf(y; y^{e_0}, …, y^{e_{s−1}})`, where `y^e` is the column `i ↦ y_i^e`. -/
noncomputable def Pfe (r : ℕ) {n s : ℕ} (y : Fin n → A) (e : Fin s → ℕ) : A :=
  Pf r y (fun k i => y i ^ e k)

/-! ### Theorem C -/

/-- **(C1)** of Theorem C in `q_pfaffian.md`: for odd `r`,
`Pf(y; c, D^−(x, ·)) = −Σ_{u=0}^{r−2} (−1)^u·x^{r−2−u}·Pf(y; c, y^u)`, where `D^−(x, ·)` is the
column `b ↦ D^−(x, y_b)`. -/
theorem C1 {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A) (x : A) :
    Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => Dab r x (y b))) =
      -∑ u ∈ range (r - 1), (-1) ^ u * x ^ (r - 2 - u) *
        Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => y b ^ u)) := by
  unfold Pf
  have e : (fun b => Dab r x (y b)) =
      fun b => ∑ u ∈ range (r - 1), (-((-1) ^ u * x ^ (r - 2 - u))) * (y b ^ u) := by
    funext b
    rw [OddShapes.A4_Dminus r hr, ← sum_neg_distrib]
    refine sum_congr rfl fun u _ => by ring
  rw [e, bpf_snoc_sum _ (ay_isAlt hr y), ← sum_neg_distrib]
  refine sum_congr rfl fun u _ => by ring

/-- **(C2)** of Theorem C in `q_pfaffian.md`: for odd `r`,
`Pf(y; c, D(x, ·)) = Σ_{u=0}^{r−1} (−1)^u·x^{r−1−u}·Pf(y; c, y^u)`, where `D = Dab (r+1)`. -/
theorem C2 {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A) (x : A) :
    Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => Dab (r + 1) x (y b))) =
      ∑ u ∈ range r, (-1) ^ u * x ^ (r - 1 - u) *
        Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => y b ^ u)) := by
  unfold Pf
  have e : (fun b => Dab (r + 1) x (y b)) =
      fun b => ∑ u ∈ range r, ((-1) ^ u * x ^ (r - 1 - u)) * (y b ^ u) := by
    funext b
    rw [OddShapes.A4_D r hr]
    refine sum_congr rfl fun u _ => by ring
  rw [e, bpf_snoc_sum _ (ay_isAlt hr y)]

/-- **(C3)** of Theorem C in `q_pfaffian.md`: for odd `r`,
`Pf(y; c, D(x, ·)) = Pf(y; c, y^{r−1}) − x·Pf(y; c, D^−(x, ·))`. -/
theorem C3 {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A) (x : A) :
    Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => Dab (r + 1) x (y b))) =
      Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => y b ^ (r - 1))) -
        x * Pf r y (Fin.snoc (α := fun _ => Fin n → A) c (fun b => Dab r x (y b))) := by
  unfold Pf
  have hr1 : 1 ≤ r := by obtain ⟨k, rfl⟩ := hr; omega
  have e : (fun b => Dab (r + 1) x (y b)) =
      fun b => y b ^ (r - 1) + (-x) * Dab r x (y b) := by
    funext b
    rw [OddShapes.A1 r hr1]; ring
  rw [e, bpf_snoc_add _ (ay_isAlt hr y)]
  ring

/-- **(C6)** of Theorem C in `q_pfaffian.md`: for odd `r` and a permutation `σ` of `Fin n`,
`Pf(y∘σ; c∘σ) = sgn(σ)·Pf(y; c)` (where `c∘σ` is the list of the columns `c_k ∘ σ`). -/
theorem C6 {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (c : Fin s → Fin n → A)
    (σ : Perm (Fin n)) :
    Pf r (fun i => y (σ i)) (fun k i => c k (σ i)) = ((Perm.sign σ : ℤ) : A) * Pf r y c :=
  bpf_perm_vars (ay r y) (ay_isAlt hr y) c σ

/-- **(C6)** of Theorem C in `q_pfaffian.md`, second part: `Pf_e(y∘σ) = sgn(σ)·Pf_e(y)`. -/
theorem C6_e {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (e : Fin s → ℕ)
    (σ : Perm (Fin n)) :
    Pfe r (fun i => y (σ i)) e = ((Perm.sign σ : ℤ) : A) * Pfe r y e :=
  C6 hr y (fun k i => y i ^ e k) σ

/-- **(C5)** of Theorem C in `q_pfaffian.md`: for odd `r` and `n = s`,
`Pf_{(0, 1, …, s−1)}(y) = (−1)^{s(s−1)/2}·Π_{i < j < s} (y_j − y_i)`. -/
theorem C5 {r : ℕ} (hr : Odd r) {s : ℕ} (y : Fin s → A) :
    Pfe r y (fun k : Fin s => (k : ℕ)) =
      (-1) ^ (s * (s - 1) / 2) * ∏ i : Fin s, ∏ j ∈ Ioi i, (y j - y i) := by
  unfold Pfe Pf
  rw [bpf_square _ (ay_isAlt hr y), ← Matrix.det_vandermonde]
  rfl

/-- Auxiliary for (C4) of `q_pfaffian.md`: the permutation of `Fin (s+1)` sending the last place to the place `p`
and `k` to `p.succAbove k` (the cyclic permutation that moves the last border to its place). -/
def insPerm {s : ℕ} (p : Fin (s + 1)) : Perm (Fin (s + 1)) :=
  p.cycleRange.symm * (Fin.last s).cycleRange

/-- Auxiliary for (C4) of `q_pfaffian.md`: `insPerm p` on the first `s` places. -/
theorem insPerm_castSucc {s : ℕ} (p : Fin (s + 1)) (k : Fin s) :
    insPerm p k.castSucc = p.succAbove k := by
  simp only [insPerm, Perm.coe_mul, Function.comp_apply,
    Fin.cycleRange_of_lt (Fin.castSucc_lt_last k), Fin.coeSucc_eq_succ, Fin.cycleRange_symm_succ]

/-- Auxiliary for (C4) of `q_pfaffian.md`: `insPerm p` sends the last place to `p`. -/
theorem insPerm_last {s : ℕ} (p : Fin (s + 1)) : insPerm p (Fin.last s) = p := by
  simp only [insPerm, Perm.coe_mul, Function.comp_apply, Fin.cycleRange_self,
    Fin.cycleRange_symm_zero]

/-- Auxiliary for (C4) of `q_pfaffian.md`: the sign of `insPerm p` is `(−1)^{s−p}`. -/
theorem sign_insPerm {s : ℕ} (p : Fin (s + 1)) :
    ((Perm.sign (insPerm p) : ℤ) : A) = (-1) ^ (s - (p : ℕ)) := by
  have hp : (p : ℕ) ≤ s := Nat.lt_succ_iff.1 p.2
  simp only [insPerm, Perm.sign_mul, Perm.sign_symm, Fin.sign_cycleRange, Fin.val_last]
  push_cast
  rw [← pow_add, show (p : ℕ) + s = (s - p) + 2 * p by omega, pow_add, pow_mul]
  simp

/-- **(C4)** of Theorem C in `q_pfaffian.md`, first part: for odd `r`, a list of exponents `e`
and an exponent `u`, `Pf(y; y^{e_0}, …, y^{e_{s−1}}, y^u) = 0` if `u` is one of the `e_k`. -/
theorem C4_eq_zero {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (e : Fin s → ℕ) (u : ℕ)
    (k : Fin s) (hk : e k = u) :
    Pf r y (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y i ^ e k) (fun i => y i ^ u)) = 0 :=
  bpf_eq_zero_of_border_eq _ (ay_isAlt hr y) _ (k := k.castSucc) (k' := Fin.last s)
    (Fin.castSucc_lt_last k).ne (by simp [hk])

/-- **(C4)** of Theorem C in `q_pfaffian.md`, second part: for odd `r`, if
`e_0 < ⋯ < e_{s−1}` and `u` is none of the `e_k`, then
`Pf(y; y^{e_0}, …, y^{e_{s−1}}, y^u) = (−1)^{#{k : e_k > u}}·Pf_{e'}(y)`, where `e'` is the
increasing list of `{e_0, …, e_{s−1}, u}` (given here as any strictly increasing
`e' : Fin (s+1) → ℕ` whose set of values is `{e_0, …, e_{s−1}, u}`; it is unique). -/
theorem C4 {r : ℕ} (hr : Odd r) {n s : ℕ} (y : Fin n → A) (e : Fin s → ℕ) (he : StrictMono e)
    (u : ℕ) (hu : ∀ k, e k ≠ u) (e' : Fin (s + 1) → ℕ) (he' : StrictMono e')
    (hrange : ∀ m, (∃ j, e' j = m) ↔ (∃ k, e k = m) ∨ m = u) :
    Pf r y (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y i ^ e k) (fun i => y i ^ u)) =
      (-1) ^ (univ.filter fun k => u < e k).card * Pfe r y e' := by
  classical
  set F := univ.filter fun k => e k < u with hF
  have hFle : F.card < s + 1 := Nat.lt_succ_of_le (by simpa using card_le_univ F)
  set p : Fin (s + 1) := ⟨F.card, hFle⟩ with hp
  have hkey : ∀ k, e k < u ↔ (k : ℕ) < p := by
    intro k
    constructor
    · intro hk
      have hsub : Finset.Iic k ⊆ F := by
        intro j hj
        simp only [hF, mem_filter, mem_univ, true_and]
        exact lt_of_le_of_lt (he.monotone (mem_Iic.1 hj)) hk
      have := card_le_card hsub
      rw [Fin.card_Iic] at this
      simp only [hp]; omega
    · intro hk
      by_contra hk'
      have hgt : u < e k := lt_of_le_of_ne (not_lt.1 hk') (Ne.symm (hu k))
      have hsub : F ⊆ Finset.Iio k := by
        intro j hj
        simp only [hF, mem_filter, mem_univ, true_and] at hj
        exact mem_Iio.2 (he.lt_iff_lt.1 (lt_trans hj hgt))
      have := card_le_card hsub
      rw [Fin.card_Iio] at this
      simp only [hp] at hk; omega
  have hins_mono : StrictMono (Fin.insertNth (α := fun _ => ℕ) p u e) := by
    intro a b hab
    induction a using Fin.succAboveCases p with
    | x =>
      induction b using Fin.succAboveCases p with
      | x => exact absurd hab (lt_irrefl _)
      | p j =>
        rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        have : ¬ (j : ℕ) < p := by
          intro h
          rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)] at hab
          exact absurd hab (not_lt.2 (le_of_lt (by simpa [Fin.lt_def] using h)))
        exact lt_of_le_of_ne (not_lt.1 (fun h => this ((hkey j).1 h))) (Ne.symm (hu j))
    | p i =>
      induction b using Fin.succAboveCases p with
      | x =>
        rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        apply (hkey i).2
        by_contra h
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)] at hab
        rw [Fin.lt_def, Fin.val_succ] at hab
        omega
      | p j =>
        rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact he (Fin.succAbove_lt_succAbove_iff.1 hab)
  have he'eq : e' = Fin.insertNth (α := fun _ => ℕ) p u e := by
    refine (he'.range_inj hins_mono).1 (Set.ext fun m => ?_)
    simp only [Set.mem_range]
    rw [hrange]
    constructor
    · rintro (⟨k, rfl⟩ | rfl)
      · exact ⟨p.succAbove k, Fin.insertNth_apply_succAbove _ _ _ _⟩
      · exact ⟨p, Fin.insertNth_apply_same _ _ _⟩
    · rintro ⟨j, rfl⟩
      induction j using Fin.succAboveCases p with
      | x => right; exact Fin.insertNth_apply_same _ _ _
      | p k => left; exact ⟨k, (Fin.insertNth_apply_succAbove (α := fun _ => ℕ) _ _ _ _).symm⟩
  have hborders : (Fin.snoc (α := fun _ => Fin n → A) (fun k i => y i ^ e k)
      (fun i => y i ^ u)) = fun k i => y i ^ e' (insPerm p k) := by
    funext k
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, insPerm_last, he'eq, Fin.insertNth_apply_same]
    | cast k =>
      rw [Fin.snoc_castSucc, insPerm_castSucc, he'eq, Fin.insertNth_apply_succAbove]
  have hcount : (univ.filter fun k => u < e k).card = s - p := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin s)))
      (fun k => e k < u)
    have e2 : (univ.filter fun k => ¬ e k < u) = univ.filter fun k => u < e k := by
      apply Finset.filter_congr
      intro k _
      exact ⟨fun h => lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hu k)), fun h => not_lt.2 h.le⟩
    rw [e2, card_univ, Fintype.card_fin] at h
    simp only [hp]
    rw [← hF] at h
    omega
  unfold Pfe Pf
  rw [hborders, bpf_perm_borders _ (ay_isAlt hr y) (fun k i => y i ^ e' k) (insPerm p),
    sign_insPerm, hcount]

end Pfaffian
