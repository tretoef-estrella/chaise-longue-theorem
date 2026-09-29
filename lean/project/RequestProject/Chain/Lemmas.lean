module

public import RequestProject.Chain.Defs

/-!
# Auxiliary lemmas for the chain lemma (`q_chain_lemma.md`)

Technical lemmas used in the proof of part (a) of the chain lemma of `q_chain_lemma.md`.
The key tool is the formula `S_t(μ) = ∑_{k=1}^{N} min(t, #{i : μ_i ≥ k})` for weakly decreasing
lists, which reduces the computation of `S_t` of an option of `μ` to counting parts `≥ k`.
-/

@[expose] public section

namespace ChainLemma

/-- Part (a) of `q_chain_lemma.md` (auxiliary): for a weakly decreasing list `l` whose entries
are all `≤ N` (expressed as: no entry is `≥ k` for `k > N`), the sum of the first `t` entries is
`∑_{k=1}^{N} min(t, #{x ∈ l : x ≥ k})`. -/
theorem sum_take_formula : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) → ∀ N,
    (∀ k, N < k → l.countP (fun x => decide (k ≤ x)) = 0) → ∀ t,
    (l.take t).sum = ∑ k ∈ Finset.Icc 1 N, min t (l.countP (fun x => decide (k ≤ x)))
  | [], _, N, _, t => by simp
  | a :: l, hl, N, hN, t => by
    rw [List.pairwise_cons] at hl
    have ha : a ≤ N := by
      by_contra h
      have := hN a (by omega)
      simp at this
    have hN' : ∀ k, N < k → l.countP (fun x => decide (k ≤ x)) = 0 := by
      intro k hk; have := hN k hk; rw [List.countP_cons] at this; omega
    cases t with
    | zero => simp
    | succ t =>
      rw [List.take_succ_cons, List.sum_cons, sum_take_formula l hl.2 N hN' t]
      have key : ∀ k ∈ Finset.Icc 1 N, min (t+1) ((a :: l).countP (fun x => decide (k ≤ x))) =
          (if k ≤ a then 1 else 0) + min t (l.countP (fun x => decide (k ≤ x))) := by
        intro k hk
        rw [List.countP_cons]
        by_cases hka : k ≤ a
        · simp [hka]; omega
        · have : l.countP (fun x => decide (k ≤ x)) = 0 := by
            rw [List.countP_eq_zero]; intro x hx; have := hl.1 x hx; simp; omega
          simp [hka, this]
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_boole]
      have : (Finset.Icc 1 N).filter (· ≤ a) = Finset.Icc 1 a := by
        ext k; simp; omega
      simp [this]

/-- Part (a) of `q_chain_lemma.md` (auxiliary): if the weakly decreasing list `l'` is obtained
from the weakly decreasing list `l` by removing one unit at level `w ≥ 1` (i.e. the number of
entries `≥ k` drops by one exactly for `k = w`), then the partial sum of the first `t` entries
drops by one exactly when `t ≥ #{x ∈ l : x ≥ w}`. -/
theorem sum_take_of_count (l l' : List ℕ) (hl : l.Pairwise (· ≥ ·)) (hl' : l'.Pairwise (· ≥ ·))
    (w : ℕ) (hw : 1 ≤ w)
    (h : ∀ k, 1 ≤ k → l'.countP (fun x => decide (k ≤ x)) + (if k = w then 1 else 0) =
      l.countP (fun x => decide (k ≤ x))) (t : ℕ) :
    (l'.take t).sum + (if l.countP (fun x => decide (w ≤ x)) ≤ t then 1 else 0) =
      (l.take t).sum := by
  set N := l.sum + w with hNdef
  have hN : ∀ k, N < k → l.countP (fun x => decide (k ≤ x)) = 0 := by
    intro k hk
    rw [List.countP_eq_zero]
    intro x hx
    have := List.le_sum_of_mem hx
    simp; omega
  have hN' : ∀ k, N < k → l'.countP (fun x => decide (k ≤ x)) = 0 := by
    intro k hk
    have h1 := h k (by omega)
    have h2 := hN k hk
    omega
  rw [sum_take_formula l hl N hN t, sum_take_formula l' hl' N hN' t]
  have hwN : w ∈ Finset.Icc 1 N := by simp; omega
  rw [← Finset.add_sum_erase _ _ hwN, ← Finset.add_sum_erase _ _ hwN]
  have hrest : ∑ k ∈ (Finset.Icc 1 N).erase w, min t (l'.countP (fun x => decide (k ≤ x))) =
      ∑ k ∈ (Finset.Icc 1 N).erase w, min t (l.countP (fun x => decide (k ≤ x))) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp at hk
    have := h k hk.2.1
    simp [hk.1] at this
    rw [this]
  rw [hrest]
  have := h w hw
  simp at this
  split_ifs <;> omega

namespace Partition

/-- Part (a) of `q_chain_lemma.md` (auxiliary): row `i` is the entry at index `i - 1`. -/
lemma row_eq_getElem (μ : Partition) (i : ℕ) (h : i - 1 < μ.parts.length) :
    μ.row i = μ.parts[i - 1] := by
  simp [row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Part (a) of `q_chain_lemma.md` (auxiliary): `μ_i = 0` for `i > ℓ`. -/
lemma row_eq_zero (μ : Partition) (i : ℕ) (h : μ.parts.length ≤ i - 1) : μ.row i = 0 := by
  simp [row, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Part (a) of `q_chain_lemma.md` (auxiliary): `S_t(μ)` is the sum of the first `t` entries of
the list of rows. -/
lemma S_eq_sum_take (μ : Partition) (t : ℕ) : S t μ = (μ.parts.take t).sum := by
  induction t with
  | zero => simp [S]
  | succ t ih =>
    rw [S, Finset.sum_Icc_succ_top (by omega), ← S, ih, List.take_add_one, List.sum_append]
    congr 1
    by_cases ht : t < μ.parts.length
    · rw [row_eq_getElem _ _ (by simpa using ht)]
      simp [List.getElem?_eq_getElem ht]
    · rw [row_eq_zero _ _ (by simp; omega)]
      simp [List.getElem?_eq_none (by omega : μ.parts.length ≤ t)]

end Partition

/-- Part (a) of `q_chain_lemma.md` (auxiliary): in a weakly decreasing list, the entries `≥ v`
form an initial segment, of length `#{x ∈ l : x ≥ v}`. -/
theorem le_getElem_iff : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) → ∀ v i (hi : i < l.length),
    (v ≤ l[i] ↔ i < l.countP (fun x => decide (v ≤ x)))
  | [], _, v, i, hi => by simp at hi
  | a :: l, hl, v, i, hi => by
    rw [List.pairwise_cons] at hl
    rw [List.countP_cons]
    by_cases hva : v ≤ a
    · cases i with
      | zero => simp [hva]
      | succ i =>
        have := le_getElem_iff l hl.2 v i (by simpa using hi)
        simp [hva, this]
    · have h0 : l.countP (fun x => decide (v ≤ x)) = 0 := by
        rw [List.countP_eq_zero]; intro x hx; have := hl.1 x hx; simp; omega
      simp only [h0, hva, decide_false]
      cases i with
      | zero => simpa using hva
      | succ i =>
        have := hl.1 _ (List.getElem_mem (by simpa using hi : i < l.length))
        simp; omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): changing one entry of a list changes the count of
entries satisfying `p` accordingly. -/
theorem countP_modify (l : List ℕ) (i : ℕ) (f : ℕ → ℕ) (p : ℕ → Bool) (h : i < l.length) :
    (l.modify i f).countP p + (if p l[i] then 1 else 0) =
      l.countP p + (if p (f l[i]) then 1 else 0) := by
  rw [List.modify_eq_take_cons_drop h]
  have hc : l.countP p = (l.take i).countP p + (l[i] :: l.drop (i + 1)).countP p := by
    rw [← List.countP_append, List.getElem_cons_drop, List.take_append_drop]
  rw [hc]
  simp only [List.countP_append, List.countP_cons]
  omega

namespace Partition

/-- Part (a) of `q_chain_lemma.md` (auxiliary): rows `1 ≤ j ≤ ℓ` are positive. -/
lemma row_pos (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) : 1 ≤ μ.row j := by
  rw [row_eq_getElem _ _ (by unfold len at hjl; omega)]
  exact μ.pos _ (List.getElem_mem _)

/-- Part (a) of `q_chain_lemma.md` (auxiliary): rows are weakly decreasing. -/
lemma row_anti (μ : Partition) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ μ.len) :
    μ.row j ≤ μ.row i := by
  unfold len at hj
  rw [row_eq_getElem _ _ (by omega), row_eq_getElem _ _ (by omega)]
  rcases Nat.lt_or_ge (i - 1) (j - 1) with h | h
  · exact List.pairwise_iff_getElem.1 μ.sorted _ _ _ _ h
  · have : i - 1 = j - 1 := by omega
    simp [this]

/-- Part (a) of `q_chain_lemma.md` (auxiliary): `r̄_j = #{i : μ_i ≥ μ_j}`. -/
lemma rbar_eq (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    μ.rbar j = μ.parts.countP (fun x => decide (μ.row j ≤ x)) := by
  set c := μ.parts.countP (fun x => decide (μ.row j ≤ x)) with hc
  have hv := μ.row_pos j hj hjl
  have hjl' : j - 1 < μ.parts.length := by unfold len at hjl; omega
  have hjc : j - 1 < c := by
    rw [hc, ← le_getElem_iff _ μ.sorted _ _ hjl', ← row_eq_getElem _ _ hjl']
  have hcl : c ≤ μ.parts.length := List.countP_le_length
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨by omega, le_antisymm ?_ ?_⟩
    · exact μ.row_anti j c hj (by omega) hcl
    · rw [row_eq_getElem μ c (by omega)]
      exact (le_getElem_iff _ μ.sorted _ _ (by omega)).2 (by omega)
  · rintro i ⟨hi1, hi⟩
    have hil : i - 1 < μ.parts.length := by
      by_contra h
      rw [row_eq_zero _ _ (by omega)] at hi
      omega
    have : μ.row j ≤ μ.parts[i - 1] := by rw [← row_eq_getElem _ _ hil, hi]
    have := (le_getElem_iff _ μ.sorted _ _ hil).1 this
    omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): `#{i : μ_i > μ_j} ≤ j - 1`. -/
lemma count_gt_le (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    μ.parts.countP (fun x => decide (μ.row j + 1 ≤ x)) ≤ j - 1 := by
  have hjl' : j - 1 < μ.parts.length := by unfold len at hjl; omega
  by_contra h
  have := (le_getElem_iff _ μ.sorted (μ.row j + 1) _ hjl').2 (by omega)
  rw [← row_eq_getElem _ _ hjl'] at this
  omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): `r̲_j = #{i : μ_i > μ_j} + 1`. -/
lemma rlow_eq (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) :
    μ.rlow j = μ.parts.countP (fun x => decide (μ.row j + 1 ≤ x)) + 1 := by
  set c := μ.parts.countP (fun x => decide (μ.row j + 1 ≤ x)) with hc
  have hcj := μ.count_gt_le j hj hjl
  have hv := μ.row_pos j hj hjl
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by omega, le_antisymm ?_ ?_⟩
    · have hcl : c < μ.parts.length := by unfold len at hjl; omega
      rw [row_eq_getElem _ _ (by simpa using hcl)]
      have := (le_getElem_iff _ μ.sorted (μ.row j + 1) _ hcl).not.2 (by omega)
      simp at this ⊢
      omega
    · exact μ.row_anti (c + 1) j (by omega) (by omega) hjl
  · rintro i ⟨hi1, hi⟩
    have hil : i - 1 < μ.parts.length := by
      by_contra h
      rw [row_eq_zero _ _ (by omega)] at hi
      omega
    have h1 : ¬ (μ.row j + 1 ≤ μ.parts[i - 1]) := by rw [← row_eq_getElem _ _ hil, hi]; omega
    have := (le_getElem_iff _ μ.sorted _ _ hil).not.1 h1
    omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): counting the parts `≥ k` of `μ − e_j`. -/
lemma countP_subE (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) (k : ℕ) (hk : 1 ≤ k) :
    (μ.subE j).parts.countP (fun x => decide (k ≤ x)) + (if k = μ.row j then 1 else 0) =
      μ.parts.countP (fun x => decide (k ≤ x)) := by
  have hjl' : j - 1 < μ.parts.length := by unfold len at hjl; omega
  have hv := μ.row_pos j hj hjl
  simp only [subE, sortDesc]
  rw [(List.mergeSort_perm _ _).countP_eq, List.countP_filter]
  have e : (μ.parts.modify (j - 1) (· - 1)).countP (fun x => decide (k ≤ x) && decide (x ≠ 0)) =
      (μ.parts.modify (j - 1) (· - 1)).countP (fun x => decide (k ≤ x)) := by
    apply List.countP_congr; intro x _; simp; omega
  rw [e]
  have := countP_modify μ.parts (j - 1) (· - 1) (fun x => decide (k ≤ x)) hjl'
  rw [← row_eq_getElem _ _ hjl'] at this
  simp only [decide_eq_true_eq] at this
  split_ifs at this ⊢ <;> omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): counting the parts `≥ k` of `μ + e_j`. -/
lemma countP_addE (μ : Partition) (j : ℕ) (hj : 1 ≤ j) (hjl : j ≤ μ.len) (k : ℕ) :
    μ.parts.countP (fun x => decide (k ≤ x)) + (if k = μ.row j + 1 then 1 else 0) =
      (μ.addE j).parts.countP (fun x => decide (k ≤ x)) := by
  have hjl' : j - 1 < μ.parts.length := by unfold len at hjl; omega
  simp only [addE, sortDesc]
  rw [(List.mergeSort_perm _ _).countP_eq]
  have := countP_modify μ.parts (j - 1) (· + 1) (fun x => decide (k ≤ x)) hjl'
  rw [← row_eq_getElem _ _ hjl'] at this
  simp only [decide_eq_true_eq] at this
  split_ifs at this ⊢ <;> omega

/-- Part (a) of `q_chain_lemma.md` (auxiliary): counting the parts `≥ k` of `μ ⊔ 1`. -/
lemma countP_addOne (μ : Partition) (k : ℕ) (hk : 1 ≤ k) :
    μ.parts.countP (fun x => decide (k ≤ x)) + (if k = 1 then 1 else 0) =
      μ.addOne.parts.countP (fun x => decide (k ≤ x)) := by
  simp only [addOne, List.countP_append]
  by_cases h : k = 1
  · simp [h]
  · have h' : ¬ k ≤ 1 := by omega
    simp [h, h']

end Partition

end ChainLemma
