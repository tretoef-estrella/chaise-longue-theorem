module

public import RequestProject.Monotone.Defs

/-!
# Auxiliary lemmas for `q_P2_monotone_options.md`

Row facts, the facts **(T)** and **(5.2)**, and the case analysis (a)–(e2) of the **Proof** of the
**Proposition** of `q_P2_monotone_options.md`.
-/

@[expose] public section

namespace ChainLemma

namespace Partition

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): rows are weakly
decreasing, including the zero rows `μ_i = 0` for `i > ℓ`. -/
lemma row_anti' (μ : Partition) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : μ.row j ≤ μ.row i := by
  by_cases hj : j ≤ μ.len
  · exact μ.row_anti i j hi hij hj
  · rw [row_eq_zero μ j (by unfold len at hj; omega)]; exact Nat.zero_le _

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `μ_i = 0` for `i > ℓ`. -/
lemma row_eq_zero' (μ : Partition) {i : ℕ} (hi : μ.len < i) : μ.row i = 0 :=
  row_eq_zero μ i (by unfold len at hi; omega)

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `S_{t+1} = S_t + μ_{t+1}`. -/
lemma S_succ (μ : Partition) (t : ℕ) : S (t + 1) μ = S t μ + μ.row (t + 1) := by
  rw [S, Finset.sum_Icc_succ_top (by omega), ← S]

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `S_t(μ) = |μ|` for
`t ≥ ℓ`. -/
lemma S_eq_size (μ : Partition) {t : ℕ} (ht : μ.len ≤ t) : S t μ = μ.size := by
  rw [S_eq_sum_take, List.take_of_length_le ht]; rfl

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary):
`S_n = S_m + Σ_{s=m+1}^{n} μ_s`. -/
lemma S_add_Ioc (μ : Partition) {m n : ℕ} (h : m ≤ n) :
    S n μ = S m μ + ∑ i ∈ Finset.Ioc m n, μ.row i := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [S_succ, ih, Finset.sum_Ioc_succ_top hmn]; ring

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary, used for (5.2)): the
non-empty rows `m+1, …, n ≤ ℓ` give `S_n ≥ S_m + (n − m)`. -/
lemma S_add_le_of_le_len (μ : Partition) {m n : ℕ} (h : m ≤ n) (hn : n ≤ μ.len) :
    S m μ + (n - m) ≤ S n μ := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [S_succ]
    have := μ.row_pos (n + 1) (by omega) hn
    have := ih (by omega)
    omega

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): comparing
`Σ_{s=m+1}^{n} μ_s` with `Σ_{s=m+1}^{n} ν_s` row by row, with one strict row. -/
lemma S_cmp_strict (μ ν : Partition) {m n : ℕ} (hmn : m ≤ n)
    (hle : ∀ s, m < s → s ≤ n → μ.row s ≤ ν.row s) (s0 : ℕ) (hs0 : m < s0) (hs0n : s0 ≤ n)
    (hlt : μ.row s0 < ν.row s0) : S n μ + S m ν < S n ν + S m μ := by
  rw [S_add_Ioc μ hmn, S_add_Ioc ν hmn]
  have : ∑ i ∈ Finset.Ioc m n, μ.row i < ∑ i ∈ Finset.Ioc m n, ν.row i :=
    Finset.sum_lt_sum (fun s hs => by simp at hs; exact hle s hs.1 hs.2)
      ⟨s0, by simp; omega, hlt⟩
  omega

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): for `1 ≤ j ≤ ℓ` and
`i ≥ 1`, `μ_i ≥ μ_j ↔ i ≤ r̄_j`. -/
lemma le_row_iff (μ : Partition) {j i : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) (hi : 1 ≤ i) :
    μ.row j ≤ μ.row i ↔ i ≤ μ.rbar j := by
  rw [μ.rbar_eq j hj hjl]
  by_cases hil : i - 1 < μ.parts.length
  · rw [row_eq_getElem μ i hil, le_getElem_iff _ μ.sorted _ _ hil]; omega
  · rw [row_eq_zero μ i (by omega)]
    have := μ.row_pos j hj hjl
    have : μ.parts.countP (fun x => decide (μ.row j ≤ x)) ≤ μ.parts.length :=
      List.countP_le_length
    constructor <;> intro <;> omega

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): for `1 ≤ j ≤ ℓ` and
`i ≥ 1`, `μ_i > μ_j ↔ i < r̲_j`. -/
lemma lt_row_iff (μ : Partition) {j i : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) (hi : 1 ≤ i) :
    μ.row j + 1 ≤ μ.row i ↔ i < μ.rlow j := by
  rw [μ.rlow_eq j hj hjl]
  have hc := μ.count_gt_le j hj hjl
  by_cases hil : i - 1 < μ.parts.length
  · rw [row_eq_getElem μ i hil, le_getElem_iff _ μ.sorted _ _ hil]; omega
  · rw [row_eq_zero μ i (by omega)]
    unfold len at hjl
    constructor <;> intro <;> omega

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `r̄_j ≥ j`. -/
lemma le_rbar (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) : j ≤ μ.rbar j :=
  (μ.le_row_iff hj hjl hj).1 le_rfl

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `r̲_j ≤ j`. -/
lemma rlow_le (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) : μ.rlow j ≤ j := by
  have := (μ.lt_row_iff hj hjl hj).not.1 (by omega)
  omega

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): rows `r̲_j, …, j` all
have length `μ_j`. -/
lemma row_eq_of_rlow_le (μ : Partition) {j s : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len)
    (hs : μ.rlow j ≤ s) (hsj : s ≤ j) : μ.row s = μ.row j := by
  have h1 : 1 ≤ s := by
    have : 1 ≤ μ.rlow j := by
      by_contra h
      have h0 : μ.rlow j = 0 := by omega
      rw [μ.rlow_eq j hj hjl] at h0
      omega
    omega
  have := (μ.lt_row_iff hj hjl h1).not.2 (by omega)
  have := μ.row_anti' h1 hsj
  omega

end Partition

open Partition

/-- Proof of the Proposition of `q_P2_monotone_options.md` (auxiliary): `λ ≼ μ` also gives
`S_0(λ) ≤ S_0(μ)` (both are `0`). -/
lemma WeakDom.le_all {μ ν : Partition} (hle : μ ≼ ν) (u : ℕ) : S u μ ≤ S u ν := by
  rcases u with _ | u
  · simp [S]
  · exact hle _ (by omega)

/-- Fact **(T)** of the Proof in `q_P2_monotone_options.md`, first half: if `t ≥ 1` is tight then
`μ_t ≥ μ̃_t`. -/
lemma tight_row_ge {μ ν : Partition} (hle : μ ≼ ν) {t : ℕ} (ht : 1 ≤ t)
    (tight : S t μ = S t ν) : ν.row t ≤ μ.row t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have := hle.le_all u
  rw [S_succ, S_succ] at tight
  omega

/-- Fact **(T)** of the Proof in `q_P2_monotone_options.md`, second half: if `t` is tight then
`μ_{t+1} ≤ μ̃_{t+1}`. -/
lemma tight_row_succ_le {μ ν : Partition} (hle : μ ≼ ν) {t : ℕ}
    (tight : S t μ = S t ν) : μ.row (t + 1) ≤ ν.row (t + 1) := by
  have := hle (t + 1) (by omega)
  rw [S_succ, S_succ] at this
  omega

/-- Estimate **(5.2)** of the Proof in `q_P2_monotone_options.md`: if `ℓ ≤ t ≤ ℓ̃` then
`S_t(μ̃) ≥ |μ| + (t − ℓ)` (stated with `S_t(μ) = |μ|`). -/
lemma gap_estimate {μ ν : Partition} (hle : μ ≼ ν) {t : ℕ} (h1 : μ.len ≤ t) (h2 : t ≤ ν.len) :
    S t μ + (t - μ.len) ≤ S t ν := by
  have e1 := S_eq_size μ h1
  have e2 := S_eq_size μ le_rfl
  have := hle.le_all μ.len
  have := ν.S_add_le_of_le_len h1 h2
  omega

/-- Proof of the Proposition of `q_P2_monotone_options.md`, common step of cases (b) and (e2): a
tight `t ≥ 1` with `t < j`, rows `t, …, j` of `μ` all equal to `μ_j`, and `μ̃_j < μ_j` is
impossible, since it would give `S_j(μ̃) < S_j(μ)`. -/
lemma no_tight_drop {μ ν : Partition} (hle : μ ≼ ν) {t j : ℕ} (ht : 1 ≤ t)
    (tight : S t μ = S t ν) (htj : t < j) (hrow : ∀ s, t ≤ s → s ≤ j → μ.row s = μ.row j)
    (hj : ν.row j < μ.row j) : False := by
  have hT := tight_row_ge hle ht tight
  have hμt := hrow t le_rfl htj.le
  have key := S_cmp_strict ν μ htj.le (fun s h1 h2 => by
    have := ν.row_anti' ht h1.le
    have := hrow s h1.le h2
    omega) j htj le_rfl hj
  have := hle j (by omega)
  omega

/-- Case **(a)** of the Proof in `q_P2_monotone_options.md`: for `p ≤ min(ℓ, ℓ̃)`,
`μ − e_p ≼ μ̃ − e_p`. -/
lemma case_a {μ ν : Partition} (hle : μ ≼ ν) {p : ℕ} (hp : 1 ≤ p) (hpμ : p ≤ μ.len)
    (hpν : p ≤ ν.len) : μ.subE p ≼ ν.subE p := by
  intro t ht
  rw [S_subE μ t p ht hp hpμ, S_subE ν t p ht hp hpν]
  have h0 := hle t ht
  have key : ν.rbar p ≤ t → t < μ.rbar p → S t μ < S t ν := by
    intro h1 h2
    by_contra hc
    have tight : S t μ = S t ν := by omega
    have hT := tight_row_succ_le hle tight
    have hpt : p ≤ t := (ν.le_rbar hp hpν).trans h1
    have hμs : ∀ s, p ≤ s → s ≤ t + 1 → μ.row s = μ.row p := fun s h1 h2 =>
      le_antisymm (μ.row_anti' hp h1) ((μ.le_row_iff hp hpμ (by omega)).2 (by omega))
    have hν : ν.row (t + 1) < ν.row p := by
      have := (ν.le_row_iff hp hpν (by omega : 1 ≤ t + 1)).not.2 (by omega)
      omega
    have hμ1 := hμs (t + 1) (by omega) le_rfl
    have k := S_cmp_strict μ ν (m := p - 1) (n := t) (by omega) (fun s h1 h2 => by
      have := hμs s (by omega) (by omega)
      have := ν.row_anti' (by omega : 1 ≤ s) (by omega : s ≤ t + 1)
      omega) p (by omega) hpt (by omega)
    have := hle.le_all (p - 1)
    omega
  split_ifs <;> omega

/-- Case **(b)** of the Proof in `q_P2_monotone_options.md`: for `j ≤ min(ℓ, ℓ̃)`,
`μ + e_j ≼ μ̃ + e_j`. -/
lemma case_b {μ ν : Partition} (hle : μ ≼ ν) {j : ℕ} (hj : 1 ≤ j) (hjμ : j ≤ μ.len)
    (hjν : j ≤ ν.len) : μ.addE j ≼ ν.addE j := by
  intro t ht
  rw [S_addE μ t j ht hj hjμ, S_addE ν t j ht hj hjν]
  have h0 := hle t ht
  have key : μ.rlow j ≤ t → t < ν.rlow j → S t μ < S t ν := by
    intro h1 h2
    by_contra hc
    have tight : S t μ = S t ν := by omega
    have htj : t < j := lt_of_lt_of_le h2 (ν.rlow_le hj hjν)
    have hrow : ∀ s, t ≤ s → s ≤ j → μ.row s = μ.row j := fun s h1' h2' =>
      μ.row_eq_of_rlow_le hj hjμ (by omega) h2'
    have hT := tight_row_ge hle ht tight
    have hν := (ν.lt_row_iff hj hjν ht).2 h2
    have := hrow t le_rfl htj.le
    exact no_tight_drop hle ht tight htj hrow (by omega)
  split_ifs <;> omega

/-- Case **(c)** of the Proof in `q_P2_monotone_options.md`: `μ ⊔ 1 ≼ μ̃ ⊔ 1`. -/
lemma case_c {μ ν : Partition} (hle : μ ≼ ν) : μ.addOne ≼ ν.addOne := by
  intro t ht
  rw [S_addOne μ t ht, S_addOne ν t ht]
  have h0 := hle t ht
  have key : μ.len < t → t ≤ ν.len → S t μ < S t ν := fun h1 h2 => by
    have := gap_estimate hle h1.le h2
    omega
  split_ifs <;> omega

/-- Case **(d1)** of the Proof in `q_P2_monotone_options.md`: for `ℓ < p ≤ ℓ̃` (using the parity
hypothesis), `μ ⊔ 1 ≼ μ̃ − e_p`. -/
lemma case_d1 {μ ν : Partition} (hle : μ ≼ ν) (hpar : μ.size % 2 = ν.size % 2) {p : ℕ}
    (hpμ : μ.len < p) (hpν : p ≤ ν.len) : μ.addOne ≼ ν.subE p := by
  intro t ht
  rw [S_addOne μ t ht, S_subE ν t p ht (by omega) hpν]
  have hA := hle t ht
  have hrb := ν.le_rbar (by omega : 1 ≤ p) hpν
  have hB : μ.len ≤ t → t ≤ ν.len → S t μ + (t - μ.len) ≤ S t ν := gap_estimate hle
  have hC1 : ν.len ≤ t → S t ν = ν.size := fun h => S_eq_size ν h
  have hC2 : μ.len ≤ t → S t μ = μ.size := fun h => S_eq_size μ h
  have hD : μ.size + (ν.len - μ.len) ≤ ν.size := by
    have := gap_estimate hle (show μ.len ≤ ν.len by omega) le_rfl
    rw [S_eq_size μ (by omega), S_eq_size ν le_rfl] at this
    exact this
  have hE : t = μ.len + 1 → t < ν.len → ν.rbar p ≤ t → S t μ + 2 ≤ S t ν := by
    intro e h1 h2
    have hp : p = μ.len + 1 := by omega
    subst e
    rw [S_succ ν, S_succ μ, row_eq_zero' μ (by omega : μ.len < μ.len + 1)]
    have := hle.le_all μ.len
    have r1 := ν.row_pos (μ.len + 1) (by omega) (by omega)
    have r2 := ν.row_pos (μ.len + 2) (by omega) (by omega)
    have r3 := ν.row_anti' (by omega : 1 ≤ μ.len + 1) (by omega : μ.len + 1 ≤ μ.len + 2)
    by_contra hc
    have : ν.row p ≤ ν.row (μ.len + 2) := by rw [hp]; omega
    have := (ν.le_row_iff (by omega : 1 ≤ p) hpν (by omega : 1 ≤ μ.len + 2)).1 this
    omega
  split_ifs <;> omega

/-- Case **(d2)** of the Proof in `q_P2_monotone_options.md`: for `ℓ < j ≤ ℓ̃`,
`μ ⊔ 1 ≼ μ̃ + e_j`. -/
lemma case_d2 {μ ν : Partition} (hle : μ ≼ ν) {j : ℕ} (hjμ : μ.len < j) (hjν : j ≤ ν.len) :
    μ.addOne ≼ ν.addE j := by
  intro t ht
  rw [S_addOne μ t ht, S_addE ν t j ht (by omega) hjν]
  have hA := hle t ht
  have hB : μ.len ≤ t → t ≤ ν.len → S t μ + (t - μ.len) ≤ S t ν := gap_estimate hle
  have hC1 : ν.len ≤ t → S t ν = ν.size := fun h => S_eq_size ν h
  have hC2 : μ.len ≤ t → S t μ = μ.size := fun h => S_eq_size μ h
  have hD : μ.size + (ν.len - μ.len) ≤ ν.size := by
    have := gap_estimate hle (show μ.len ≤ ν.len by omega) le_rfl
    rw [S_eq_size μ (by omega), S_eq_size ν le_rfl] at this
    exact this
  split_ifs <;> omega

/-- Case **(e1)** of the Proof in `q_P2_monotone_options.md`: for `p ≤ ℓ`,
`μ − e_p ≼ μ ≼ μ̃ ≼ μ̃ ⊔ 1` (by part (a) of `q_chain_lemma.md`). -/
lemma case_e1 {μ ν : Partition} (hle : μ ≼ ν) {p : ℕ} (hp : 1 ≤ p) (hpμ : p ≤ μ.len) :
    μ.subE p ≼ ν.addOne :=
  ((μ.subE_le_self p hp hpμ).trans hle).trans ν.self_le_addOne

/-- Case **(e2)** of the Proof in `q_P2_monotone_options.md`: for `ℓ̃ < j ≤ ℓ`,
`μ + e_j ≼ μ̃ ⊔ 1`. -/
lemma case_e2 {μ ν : Partition} (hle : μ ≼ ν) {j : ℕ} (hjν : ν.len < j) (hjμ : j ≤ μ.len) :
    μ.addE j ≼ ν.addOne := by
  intro t ht
  rw [S_addE μ t j ht (by omega) hjμ, S_addOne ν t ht]
  have h0 := hle t ht
  have key : μ.rlow j ≤ t → t ≤ ν.len → S t μ < S t ν := by
    intro h1 h2
    by_contra hc
    have tight : S t μ = S t ν := by omega
    have hrow : ∀ s, t ≤ s → s ≤ j → μ.row s = μ.row j := fun s h1' h2' =>
      μ.row_eq_of_rlow_le (by omega) hjμ (by omega) h2'
    have := μ.row_pos j (by omega) hjμ
    have := row_eq_zero' ν hjν
    exact no_tight_drop hle ht tight (by omega) hrow (by omega)
  split_ifs <;> omega

end ChainLemma
