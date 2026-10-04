module

public import RequestProject.OddLayers.Defs

/-!
# Rows of a partition, through its multiset of parts

Auxiliary facts for the proof of (E) of Theorem L of `q_oddbox_layers.md`.

The proof of (E) uses part (a) of `q_chain_lemma.md`: `μ − e_j` lowers the **last** row of length
`μ_j`, `μ + e_j` raises the **first** row of length `μ_j`; and lowering or raising two different
rows commutes. Here this is expressed through the multiset of parts (`subE_eq`, `addE_eq`,
`addOne_eq` of `RequestProject/Fibres/Lemmas.lean`): the partitions `μ − e_j` and `μ + e_j` only
depend on the value `μ_j`, and the last (first) row of value `x` is the row
`#{parts ≥ x}` (`#{parts > x} + 1`).
-/

@[expose] public section

namespace OddLayers

open ChainLemma ChainLemma.Partition Fibres OddShapes

/-- Helper for (E) of `q_oddbox_layers.md`: the count of an element after erasing one copy of
`a` (truncated subtraction makes this hold also when `a` is absent). -/
lemma count_erase' (s : Multiset ℕ) (a b : ℕ) :
    (s.erase a).count b = s.count b - if b = a then 1 else 0 := by
  split_ifs with h
  · subst h; exact Multiset.count_erase_self _ _
  · rw [Multiset.count_erase_of_ne h]; simp

/-- Helper for (E) of `q_oddbox_layers.md`: the multiset of parts of a partition. -/
abbrev pm (μ : Partition) : Multiset ℕ := (μ.parts : Multiset ℕ)

/-- Helper for (E) of `q_oddbox_layers.md`: a partition has no part `0`. -/
lemma count_zero_pm (μ : Partition) : (pm μ).count 0 = 0 :=
  Multiset.count_eq_zero.mpr fun h => by simpa using μ.pos 0 (by simpa using h)

/-- Helper for (E) of `q_oddbox_layers.md`: `ℓ(μ)` is the number of parts. -/
lemma len_eq_card (μ : Partition) : μ.len = Multiset.card (pm μ) := by
  simp [Partition.len]

/-- Helper for (E) of `q_oddbox_layers.md`: the parts of `μ − e_j` (part (a) of
`q_chain_lemma.md`, through `subE_eq`). -/
lemma pm_subE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    pm (μ.subE j) = ((pm μ).erase (μ.row j) + {μ.row j - 1}).filter (0 < ·) := by
  rw [subE_eq μ hj1 hj, pm, ofMultiset_parts]

/-- Helper for (E) of `q_oddbox_layers.md`: the parts of `μ + e_j` (part (a) of
`q_chain_lemma.md`, through `addE_eq`). -/
lemma pm_addE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    pm (μ.addE j) = ((pm μ).erase (μ.row j) + {μ.row j + 1}).filter (0 < ·) := by
  rw [addE_eq μ hj1 hj, pm, ofMultiset_parts]

/-- Helper for (E) of `q_oddbox_layers.md`: the parts of `μ ⊔ 1` (through `addOne_eq`). -/
lemma pm_addOne (μ : Partition) : pm μ.addOne = (pm μ + {1}).filter (0 < ·) := by
  rw [addOne_eq μ, pm, ofMultiset_parts]

/-- Helper for (E) of `q_oddbox_layers.md`: on a weakly decreasing list, an upward closed
predicate holds exactly on an initial segment, of length its number of occurrences. -/
lemma getElem_iff_lt_countP (q : ℕ → Bool) (hq : ∀ a b, q a = true → a ≤ b → q b = true) :
    ∀ (l : List ℕ), l.Pairwise (· ≥ ·) → ∀ (i : ℕ) (hi : i < l.length),
      (q l[i] = true ↔ i < l.countP q)
  | [], _, i, hi => by simp at hi
  | b :: t, hl, i, hi => by
    rw [List.pairwise_cons] at hl
    have hzero : q b = false → t.countP q = 0 := by
      intro hb
      rw [List.countP_eq_zero]
      intro c hc hqc
      have := hq c b hqc (hl.1 c hc)
      simp_all
    rw [List.countP_cons]
    cases i with
    | zero =>
      cases hb : q b
      · simp [hzero hb, hb]
      · simp [hb]
    | succ k =>
      have ih := getElem_iff_lt_countP q hq t hl.2 k (by simpa using hi)
      simp only [List.getElem_cons_succ]
      cases hb : q b
      · have h0 := hzero hb
        rw [h0] at ih
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, h0]
        constructor
        · intro h; exact absurd (ih.mp h) (by omega)
        · intro h; omega
      · simp only [↓reduceIte]
        rw [ih]; omega

/-- Helper for (E) of `q_oddbox_layers.md`: the number of parts `≥ x`; for a part `x` this is the
last row of value `x`. -/
def cge (μ : Partition) (x : ℕ) : ℕ := Multiset.card ((pm μ).filter (x ≤ ·))

/-- Helper for (E) of `q_oddbox_layers.md`: the number of parts `> x`; for a part `x`, plus one,
this is the first row of value `x`. -/
def cgt (μ : Partition) (x : ℕ) : ℕ := Multiset.card ((pm μ).filter (x < ·))

/-- Helper for (E) of `q_oddbox_layers.md`: `cge` as a count on the list of rows. -/
lemma cge_eq_countP (μ : Partition) (x : ℕ) :
    cge μ x = μ.parts.countP (fun b => decide (x ≤ b)) := by
  rw [cge, ← Multiset.countP_eq_card_filter, Multiset.coe_countP]

/-- Helper for (E) of `q_oddbox_layers.md`: `cgt` as a count on the list of rows. -/
lemma cgt_eq_countP (μ : Partition) (x : ℕ) :
    cgt μ x = μ.parts.countP (fun b => decide (x < b)) := by
  rw [cgt, ← Multiset.countP_eq_card_filter, Multiset.coe_countP]

/-- Helper for (E) of `q_oddbox_layers.md`: the rows `≥ x` are the first `#{parts ≥ x}` rows. -/
lemma row_le_iff (μ : Partition) (x i : ℕ) (hi : i < μ.parts.length) :
    x ≤ μ.parts[i] ↔ i < cge μ x := by
  rw [cge_eq_countP]
  have := getElem_iff_lt_countP (fun b => decide (x ≤ b))
    (fun a b ha hab => by simp at ha ⊢; omega) μ.parts μ.sorted i hi
  simpa using this

/-- Helper for (E) of `q_oddbox_layers.md`: the rows `> x` are the first `#{parts > x}` rows. -/
lemma row_lt_iff (μ : Partition) (x i : ℕ) (hi : i < μ.parts.length) :
    x < μ.parts[i] ↔ i < cgt μ x := by
  rw [cgt_eq_countP]
  have := getElem_iff_lt_countP (fun b => decide (x < b))
    (fun a b ha hab => by simp at ha ⊢; omega) μ.parts μ.sorted i hi
  simpa using this

/-- Helper for (E) of `q_oddbox_layers.md`: the rows of a partition weakly decrease. -/
lemma getElem_antitone (μ : Partition) {i k : ℕ} (hik : i ≤ k) (hk : k < μ.parts.length) :
    μ.parts[k] ≤ μ.parts[i] := by
  rcases Nat.eq_or_lt_of_le hik with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp μ.sorted i k (by omega) hk hlt

/-- Helper for (E) of `q_oddbox_layers.md`: `#{parts ≥ x} ≤ ℓ(μ)`. -/
lemma cge_le_len (μ : Partition) (x : ℕ) : cge μ x ≤ μ.len := by
  rw [cge, len_eq_card]; exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- Helper for (E) of `q_oddbox_layers.md`: for a part `x` of `μ`, the row `#{parts ≥ x}`
(the last row of value `x`) has value `x`. -/
lemma row_cge (μ : Partition) {x : ℕ} (hx : x ∈ pm μ) :
    1 ≤ cge μ x ∧ cge μ x ≤ μ.len ∧ μ.row (cge μ x) = x := by
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp (Multiset.mem_coe.mp hx)
  have hkc : k < cge μ x := (row_le_iff μ x k hk).mp hkx.ge
  have hc := cge_le_len μ x
  refine ⟨by omega, hc, ?_⟩
  have hi : cge μ x - 1 < μ.parts.length := by unfold Partition.len at hc; omega
  rw [row_eq_getElem _ _ hi]
  have h1 := (row_le_iff μ x _ hi).mpr (by omega)
  have h2 := getElem_antitone μ (show k ≤ cge μ x - 1 by omega) hi
  omega

/-- Helper for (E) of `q_oddbox_layers.md`: for a part `x` of `μ`, the row `#{parts > x} + 1`
(the first row of value `x`) has value `x`. -/
lemma row_cgt (μ : Partition) {x : ℕ} (hx : x ∈ pm μ) :
    cgt μ x + 1 ≤ μ.len ∧ μ.row (cgt μ x + 1) = x := by
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp (Multiset.mem_coe.mp hx)
  have hkc : ¬ k < cgt μ x := fun h => by
    have := (row_lt_iff μ x k hk).mpr h; omega
  have hi : cgt μ x < μ.parts.length := by omega
  refine ⟨by unfold Partition.len; omega, ?_⟩
  rw [row_eq_getElem _ _ (by simpa using hi)]
  simp only [Nat.add_sub_cancel]
  have h1 : ¬ x < μ.parts[cgt μ x] := fun h => absurd ((row_lt_iff μ x _ hi).mp h) (by omega)
  have h2 := getElem_antitone μ (show cgt μ x ≤ k by omega) hk
  omega

/-- Helper for (E) of `q_oddbox_layers.md`: a row `p` lies between the first and the last row of
its value. -/
lemma le_cge_row (μ : Partition) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ μ.len) :
    p ≤ cge μ (μ.row p) ∧ cgt μ (μ.row p) + 1 ≤ p := by
  have hi : p - 1 < μ.parts.length := by unfold Partition.len at hp; omega
  rw [row_eq_getElem _ _ hi]
  have h1 := (row_le_iff μ μ.parts[p - 1] _ hi).mp le_rfl
  have h2 : ¬ p - 1 < cgt μ μ.parts[p - 1] := fun h =>
    absurd ((row_lt_iff μ _ _ hi).mpr h) (lt_irrefl _)
  omega

/-- Helper for (E) of `q_oddbox_layers.md`: membership through counts. -/
lemma mem_pm_iff (μ : Partition) (x : ℕ) : x ∈ pm μ ↔ 0 < (pm μ).count x :=
  Multiset.count_pos.symm

/-- Helper for (E) of `q_oddbox_layers.md`: two partitions with the same counts of all parts are
equal. -/
lemma eq_of_count (μ κ : Partition) (h : ∀ b, (pm μ).count b = (pm κ).count b) : μ = κ :=
  Partition.eq_of_coe_parts (Multiset.ext.mpr h)

/-- Helper for (E) of `q_oddbox_layers.md`: the number of elements of a multiset satisfying a
predicate, before and after erasing a member `a`. -/
lemma card_filter_erase (P : Multiset ℕ) (q : ℕ → Prop) [DecidablePred q] {a : ℕ} (ha : a ∈ P) :
    Multiset.card ((P.erase a).filter q) + (if q a then 1 else 0) =
      Multiset.card (P.filter q) := by
  conv_rhs => rw [← Multiset.cons_erase ha]
  rw [Multiset.filter_cons]
  split_ifs <;> simp [add_comm]

/-- Helper for (E) of `q_oddbox_layers.md`: `#{parts ≥ x} = #{parts > x} + #{parts = x}`. -/
lemma cge_eq_cgt_add_count (μ : Partition) (x : ℕ) : cge μ x = cgt μ x + (pm μ).count x := by
  unfold cge cgt
  generalize pm μ = s
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.count_cons]
    split_ifs <;> simp <;> omega

/-- Helper for (E) of `q_oddbox_layers.md`: every part is `≥ 1`. -/
lemma cge_one (μ : Partition) : cge μ 1 = μ.len := by
  rw [cge, len_eq_card, Multiset.filter_eq_self.mpr]
  intro b hb
  exact μ.pos b (by simpa using hb)

end OddLayers
