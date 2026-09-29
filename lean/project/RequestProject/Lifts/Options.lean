module

public import RequestProject.Lifts.Defs
public import RequestProject.Monotone.Lemmas

/-!
# The combinatorial part of the proof of `q_P3_lifts.md`

**Step 0** (the options stay in `Par_m`, and the positions `p` with `opt_p(μ) ∈ Λ` form the
initial segment `1, …, Φ`) and the combinatorial content of the cases **(α)**, **(β)**, **(γ)**
of the **Proof** of the Proposition of `q_P3_lifts.md`: which option `λ ∈ Λ` is used, and how its
column lengths compare with those of `μ`.
-/

@[expose] public section

namespace Lifts

open ChainLemma ChainLemma.Partition Tight

/-- Column lengths as a count (auxiliary for the cases (α), (β), (γ) of the Proof in
`q_P3_lifts.md`): `λ'_c = #{i : λ_i ≥ c}`. -/
lemma colLen_eq_countP (lam : Partition) (c : ℕ) :
    colLen lam c = lam.parts.countP (fun x => decide (c ≤ x)) := by
  unfold colLen; rw [List.countP_eq_length_filter]

/-- Case (α) of the Proof in `q_P3_lifts.md`: the columns of `μ + e_j` are those of `μ`, except
that column `μ_j + 1` is one longer. -/
lemma colLen_addE (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) (c : ℕ) :
    colLen (μ.addE j) c = colLen μ c + if c = μ.row j + 1 then 1 else 0 := by
  rw [colLen_eq_countP, colLen_eq_countP]; exact (μ.countP_addE j hj hjl c).symm

/-- Case (γ) of the Proof in `q_P3_lifts.md`: the columns of `μ − e_j` are those of `μ`, except
that column `μ_j` is one shorter. -/
lemma colLen_subE (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) {c : ℕ} (hc : 1 ≤ c) :
    colLen (μ.subE j) c + (if c = μ.row j then 1 else 0) = colLen μ c := by
  rw [colLen_eq_countP, colLen_eq_countP]; exact μ.countP_subE j hj hjl c hc

/-- Case (β) of the Proof in `q_P3_lifts.md`: the columns of `μ ⊔ 1` are those of `μ`, except
that column `1` is one longer. -/
lemma colLen_addOne (μ : Partition) {c : ℕ} (hc : 1 ≤ c) :
    colLen μ.addOne c = colLen μ c + if c = 1 then 1 else 0 := by
  rw [colLen_eq_countP, colLen_eq_countP]; exact (μ.countP_addOne c hc).symm

/-- Case (β) of the Proof in `q_P3_lifts.md`: column `1` of `μ` has height `ℓ`. -/
lemma colLen_one (μ : Partition) : colLen μ 1 = μ.len := by
  rw [colLen_eq_countP, List.countP_eq_length.2]
  · rfl
  · intro x hx; simpa using μ.pos x hx

/-- Step 1 of the Proof in `q_P3_lifts.md` (blocks `B_c` exist only for `c ≤ μ_1`): a column
`c > μ_1` is empty. -/
lemma colLen_eq_zero (μ : Partition) {c : ℕ} (hc : μ.row 1 < c) : colLen μ c = 0 := by
  rw [colLen_eq_countP, List.countP_eq_zero]
  intro x hx
  obtain ⟨parts, sorted, pos⟩ := μ
  cases parts with
  | nil => simp at hx
  | cons a l =>
    simp only [Partition.row] at hc
    simp only [List.mem_cons] at hx
    simp only [decide_eq_true_eq, not_le]
    rcases hx with rfl | hx
    · simpa using hc
    · have := (List.pairwise_cons.1 sorted).1 x hx
      simp at hc; omega

/-- Case (α) of the Proof in `q_P3_lifts.md`: if `j` is the first row of its length
(`μ_{j−1} > μ_j` when `j ≥ 2`), the column `c* = μ_j + 1` of `μ` has height `j − 1`. -/
lemma colLen_row_succ (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len)
    (hfirst : 2 ≤ j → μ.row j < μ.row (j - 1)) : colLen μ (μ.row j + 1) = j - 1 := by
  have h1 := μ.rlow_eq j hj hjl
  have h2 := μ.rlow_le hj hjl
  rw [colLen_eq_countP]
  by_contra hne
  have hlt : μ.rlow j ≤ j - 1 := by omega
  have := μ.row_eq_of_rlow_le hj hjl hlt (by omega)
  have := hfirst (by omega)
  omega

/-- Case (γ) of the Proof in `q_P3_lifts.md`: if `r` is the last row of its length
(`μ_{r+1} < μ_r`, with `μ_{ℓ+1} = 0`), the column `c = μ_r` of `μ` has height `r`. -/
lemma colLen_row (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len)
    (hlast : j < μ.len → μ.row (j + 1) < μ.row j) : colLen μ (μ.row j) = j := by
  have h1 := μ.rbar_eq j hj hjl
  have h2 := μ.le_rbar hj hjl
  rw [colLen_eq_countP, ← h1]
  by_contra hne
  have h3 := (μ.le_row_iff hj hjl (i := j + 1) (by omega)).2 (by omega)
  rcases Nat.lt_or_ge j μ.len with h | h
  · have := hlast h; omega
  · have := μ.row_eq_zero' (i := j + 1) (by omega)
    have := μ.row_pos j hj hjl
    omega

/-- Step 0 of the Proof in `q_P3_lifts.md`: `ℓ(μ + e_j) = ℓ(μ)`. -/
lemma len_addE (μ : Partition) (j : ℕ) : (μ.addE j).len = μ.len := by
  simp [addE, len, sortDesc, List.length_mergeSort, List.length_modify]

/-- Step 0 of the Proof in `q_P3_lifts.md`: `ℓ(μ − e_j) ≤ ℓ(μ)`. -/
lemma len_subE_le (μ : Partition) (j : ℕ) : (μ.subE j).len ≤ μ.len := by
  simp only [subE, len, sortDesc, List.length_mergeSort]
  exact (List.length_filter_le _ _).trans (by simp)

/-- Step 0 of the Proof in `q_P3_lifts.md`: `ℓ(μ ⊔ 1) = ℓ(μ) + 1`. -/
lemma len_addOne (μ : Partition) : μ.addOne.len = μ.len + 1 := by
  simp [addOne, len]

/-- Step 0 of the Proof in `q_P3_lifts.md`: `|μ + e_j| = |μ| + 1`. -/
lemma size_addE (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    (μ.addE j).size = μ.size + 1 := by
  rw [← S_eq_size (μ.addE j) (t := μ.len) (by rw [len_addE]), ← S_eq_size μ le_rfl,
    S_addE μ μ.len j (by omega) hj hjl, if_pos ((μ.rlow_le hj hjl).trans hjl)]

/-- Step 0 of the Proof in `q_P3_lifts.md`: `|μ − e_j| = |μ| − 1` (and `|μ| ≥ 1`). -/
lemma size_subE (μ : Partition) {j : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    (μ.subE j).size + 1 = μ.size := by
  have hr : μ.rbar j ≤ μ.len := by
    rw [μ.rbar_eq j hj hjl]; exact List.countP_le_length
  have hsz : μ.len ≤ μ.size := by
    have := μ.S_add_le_of_le_len (m := 0) (n := μ.len) (Nat.zero_le _) le_rfl
    rw [S_eq_size μ le_rfl] at this; simpa [S] using this
  rw [← S_eq_size (μ.subE j) (t := μ.len) (len_subE_le μ j), ← S_eq_size μ le_rfl,
    S_subE μ μ.len j (by omega) hj hjl, if_pos hr]
  have hsz' : μ.len ≤ S μ.len μ := by rw [S_eq_size μ le_rfl]; exact hsz
  omega

/-- Step 0 of the Proof in `q_P3_lifts.md`: `|μ ⊔ 1| = |μ| + 1`. -/
lemma size_addOne (μ : Partition) : μ.addOne.size = μ.size + 1 := by
  simp [addOne, size, List.sum_append]

/-- **Step 0** of the Proof in `q_P3_lifts.md`: for `μ ∈ Par_{m−1}` (here `m − 1 = n`) every
option `opt_p(μ)`, `p = 1, …, L` (`L = 2h`), lies in `Par_m`. -/
theorem opt_mem_Par {h n : ℕ} {μ : Partition} (hμ : μ ∈ Par h n) {p : ℕ} (hp : 1 ≤ p)
    (hpL : p ≤ 2 * h) : μ.opt (2 * h) p ∈ Par h (n + 1) := by
  obtain ⟨h1, h2, h3⟩ := hμ
  unfold opt
  split_ifs with ha hb
  · have := size_subE μ hp ha
    have := len_subE_le μ p
    refine ⟨by omega, by omega, by omega⟩
  · rw [Par, Set.mem_setOf_eq, size_addOne, len_addOne]
    refine ⟨by omega, by omega, by omega⟩
  · rw [Par, Set.mem_setOf_eq, size_addE μ (by omega) (by omega), len_addE]
    refine ⟨by omega, by omega, by omega⟩

/-- Step 0 of the Proof in `q_P3_lifts.md` ("rows of equal length give equal options"): if
`μ_j = μ_{j'}` then `μ + e_j ≼ μ + e_{j'}`. -/
lemma addE_le_of_row_eq (μ : Partition) {j j' : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) (hj' : 1 ≤ j')
    (hjl' : j' ≤ μ.len) (hrow : μ.row j = μ.row j') : μ.addE j ≼ μ.addE j' := by
  intro t ht
  have : μ.rlow j = μ.rlow j' := by unfold rlow; rw [hrow]
  rw [S_addE μ t j ht hj hjl, S_addE μ t j' ht hj' hjl', this]

/-- Step 0 of the Proof in `q_P3_lifts.md` ("rows of equal length give equal options"): if
`μ_j = μ_{j'}` then `μ − e_j ≼ μ − e_{j'}`. -/
lemma subE_le_of_row_eq (μ : Partition) {j j' : ℕ} (hj : 1 ≤ j) (hjl : j ≤ μ.len) (hj' : 1 ≤ j')
    (hjl' : j' ≤ μ.len) (hrow : μ.row j = μ.row j') : μ.subE j ≼ μ.subE j' := by
  intro t ht
  have : μ.rbar j = μ.rbar j' := by unfold rbar; rw [hrow]
  rw [S_subE μ t j ht hj hjl, S_subE μ t j' ht hj' hjl', this]

/-- **Step 0** of the Proof in `q_P3_lifts.md`: for a down-set `Λ` of `Par_m` and `μ ∈ Par_{m−1}`,
the proof of part (c) of `q_chain_lemma.md` applies: the positions `p ∈ {1, …, L}` with
`opt_p(μ) ∈ Λ` are exactly `1, …, Φ` with `Φ = F_Λ(μ)`.  (Part (c) is applied to the down-set
`{λ : λ ≼ ν for some ν ∈ Λ}`, which has the same options in it by the first half of Step 0.) -/
theorem opt_mem_iff {h n : ℕ} {Λ : Set Partition} (hΛ : IsDownSetPar h (n + 1) Λ)
    {μ : Partition} (hμ : μ ∈ Par h n) {p : ℕ} (hp : 1 ≤ p) (hpL : p ≤ 2 * h) :
    μ.opt (2 * h) p ∈ Λ ↔ p ≤ Fibres.FLam h Λ μ := by
  classical
  set Λ' : Set Partition := {x | ∃ ν ∈ Λ, x ≼ ν} with hΛ'
  have hdown : IsDownSet Λ' := by
    rintro a b hab ⟨ν, hν, hbν⟩
    exact ⟨ν, hν, hab.trans hbν⟩
  have hL : 2 * μ.len ≤ 2 * h := by have := hμ.2.2; omega
  have key := opt_mem_initial_segment μ (2 * h) hL Λ' hdown
  have hiff : ∀ p ∈ Finset.Icc 1 (2 * h), μ.opt (2 * h) p ∈ Λ ↔ μ.opt (2 * h) p ∈ Λ' := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    refine ⟨fun h1 => ⟨_, h1, WeakDom.refl _⟩, ?_⟩
    rintro ⟨ν, hν, hle⟩
    exact hΛ.2 _ ν (opt_mem_Par hμ hp.1 hp.2) hle hν
  have hfil : (Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ) =
      (Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ') :=
    Finset.filter_congr hiff
  have hF : Fibres.FLam h Λ μ =
      ((Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ')).card := by
    rw [← hfil, Fibres.FLam]
  rw [hiff p (Finset.mem_Icc.2 ⟨hp, hpL⟩), hF]
  have hmem : p ∈ (Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ') ↔
      μ.opt (2 * h) p ∈ Λ' := by simp [Finset.mem_filter, hp, hpL]
  rw [← hmem, key, Finset.mem_Icc]
  simp [hp]

/-- `F_Λ(μ) ≤ L = 2h` (used in Step 1 of the Proof in `q_P3_lifts.md`). -/
lemma FLam_le (h : ℕ) (Λ : Set Partition) (μ : Partition) : Fibres.FLam h Λ μ ≤ 2 * h := by
  classical
  unfold Fibres.FLam
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- The combinatorial content of the three cases **(α)**, **(β)**, **(γ)** of Step 1 of the Proof
in `q_P3_lifts.md`, for `μ ∈ Par_{m−1}` with `Φ = F_Λ(μ) ≥ 1`:
* cases (α) and (β): some `λ ∈ Λ` (namely `μ + e_{j_0}`, resp. `μ ⊔ 1`) has the columns of `μ`
  except that a column `c* ≥ 1` is one longer, and the height of column `c*` of `μ` is
  `L − Φ` (`= j_0 − 1`, resp. `= ℓ`);
* case (γ): some `λ ∈ Λ` (namely `μ − e_r`, `r = Φ`) has the columns of `μ` except that a column
  `c ≥ 1` is one shorter, and the height of column `c` of `μ` is `Φ` (`= r`). -/
theorem cases_of_FLam {h n : ℕ} {Λ : Set Partition} (hΛ : IsDownSetPar h (n + 1) Λ)
    {μ : Partition} (hμ : μ ∈ Par h n) (hΦ : 1 ≤ Fibres.FLam h Λ μ) :
    (∃ lam ∈ Λ, ∃ cs, 1 ≤ cs ∧
        (∀ c, 1 ≤ c → colLen lam c = colLen μ c + if c = cs then 1 else 0) ∧
        colLen μ cs + Fibres.FLam h Λ μ = 2 * h) ∨
    (∃ lam ∈ Λ, ∃ c0, 1 ≤ c0 ∧
        (∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen μ c) ∧
        colLen μ c0 = Fibres.FLam h Λ μ) := by
  set Φ := Fibres.FLam h Λ μ with hΦdef
  have hΦL : Φ ≤ 2 * h := FLam_le h Λ μ
  have hlh : μ.len ≤ h := hμ.2.2
  have hin : ∀ p, 1 ≤ p → p ≤ 2 * h → (μ.opt (2 * h) p ∈ Λ ↔ p ≤ Φ) :=
    fun p hp hpL => opt_mem_iff hΛ hμ hp hpL
  have hoptΦ := (hin Φ hΦ hΦL).2 le_rfl
  by_cases hγ : Φ ≤ μ.len
  · -- case (γ)
    right
    have hopt : μ.opt (2 * h) Φ = μ.subE Φ := by unfold opt; rw [if_pos hγ]
    rw [hopt] at hoptΦ
    refine ⟨_, hoptΦ, μ.row Φ, μ.row_pos Φ hΦ hγ, fun c hc => colLen_subE μ hΦ hγ hc, ?_⟩
    refine colLen_row μ hΦ hγ (fun hlt => ?_)
    have hle := μ.row_anti Φ (Φ + 1) hΦ (by omega) hlt
    by_contra hne
    have heq : μ.row (Φ + 1) = μ.row Φ := by omega
    have hopt' : μ.opt (2 * h) (Φ + 1) = μ.subE (Φ + 1) := by unfold opt; rw [if_pos (by omega)]
    have hmem : μ.opt (2 * h) (Φ + 1) ∈ Λ := by
      rw [hopt']
      refine hΛ.2 _ _ ?_ (subE_le_of_row_eq μ (by omega) hlt hΦ hγ heq) hoptΦ
      rw [← hopt']; exact opt_mem_Par hμ (by omega) (by omega)
    have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
    omega
  · left
    by_cases hβ : Φ ≤ 2 * h - μ.len
    · -- case (β)
      have hopt : μ.opt (2 * h) Φ = μ.addOne := by unfold opt; rw [if_neg hγ, if_pos hβ]
      rw [hopt] at hoptΦ
      refine ⟨_, hoptΦ, 1, le_rfl, fun c hc => colLen_addOne μ hc, ?_⟩
      rw [colLen_one]
      by_contra hne
      have hopt' : μ.opt (2 * h) (Φ + 1) = μ.addOne := by
        unfold opt; rw [if_neg (by omega), if_pos (by omega)]
      have := (hin (Φ + 1) (by omega) (by omega)).1 (hopt' ▸ hoptΦ)
      omega
    · -- case (α)
      set j0 := 2 * h + 1 - Φ with hj0
      have hj01 : 1 ≤ j0 := by omega
      have hj0l : j0 ≤ μ.len := by omega
      have hopt : μ.opt (2 * h) Φ = μ.addE j0 := by unfold opt; rw [if_neg hγ, if_neg hβ]
      rw [hopt] at hoptΦ
      refine ⟨_, hoptΦ, μ.row j0 + 1, by omega, fun c _ => colLen_addE μ hj01 hj0l c, ?_⟩
      rw [colLen_row_succ μ hj01 hj0l (fun h2 => ?_)]
      · omega
      have hle := μ.row_anti (j0 - 1) j0 (by omega) (by omega) hj0l
      by_contra hne
      have heq : μ.row (j0 - 1) = μ.row j0 := by omega
      have hopt' : μ.opt (2 * h) (Φ + 1) = μ.addE (j0 - 1) := by
        unfold opt; rw [if_neg (by omega), if_neg (by omega)]; congr 1
      have hmem : μ.opt (2 * h) (Φ + 1) ∈ Λ := by
        rw [hopt']
        refine hΛ.2 _ _ ?_ (addE_le_of_row_eq μ (by omega) (by omega) hj01 hj0l heq) hoptΦ
        rw [← hopt']; exact opt_mem_Par hμ (by omega) (by omega)
      have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
      omega

end Lifts

end
