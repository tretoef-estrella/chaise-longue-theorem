module

public import Mathlib

/-!
# Definitions for the chain lemma (`q_chain_lemma.md`)

This file formalizes the **Setting** section of `q_chain_lemma.md`: partitions, the partial sums
`S_t`, weak dominance `≼`, the operations `μ − e_j`, `μ + e_j`, `μ ⊔ 1`, the rows `r̄_j`, `r̲_j`,
the list of options `opt_p(μ)` and down-sets.

**Encoding of partitions.** A partition is encoded as a `List ℕ` (the list of rows
`[μ_1, μ_2, …, μ_ℓ]`) that is weakly decreasing, i.e. `List.Pairwise (· ≥ ·)` (this is what
`List.Sorted (· ≥ ·)` unfolds to; `List.Sorted` is a deprecated alias of `List.Pairwise` in the
current Mathlib), and whose entries are all positive. Rows are indexed from `1` as in the file.
-/

@[expose] public section

namespace ChainLemma

/-- **Setting, "Partitions"** of `q_chain_lemma.md`: a partition
`μ = (μ_1 ≥ μ_2 ≥ ⋯ ≥ μ_ℓ)` of positive integers, encoded as the list `parts = [μ_1, …, μ_ℓ]`,
which is weakly decreasing (`List.Pairwise (· ≥ ·)`, i.e. `Sorted (· ≥ ·)`) and has all entries
positive. The empty partition is the empty list. Used in parts (a), (b) and (c). -/
@[ext]
structure Partition where
  /-- The rows `[μ_1, …, μ_ℓ]` of the partition. -/
  parts : List ℕ
  /-- The rows are weakly decreasing: `μ_1 ≥ μ_2 ≥ ⋯ ≥ μ_ℓ`. -/
  sorted : parts.Pairwise (· ≥ ·)
  /-- All rows are positive. -/
  pos : ∀ x ∈ parts, 0 < x

namespace Partition

/-- **Setting, "Partitions"** of `q_chain_lemma.md`: the length `ℓ = ℓ(μ)` (number of rows). Used in parts (a), (b) and (c). -/
def len (μ : Partition) : ℕ := μ.parts.length

/-- **Setting, "Partitions"** of `q_chain_lemma.md`: the row `μ_i` for `i ≥ 1`, with the
convention `μ_i := 0` for `i > ℓ`. (Rows are indexed from `1`; the value at `i = 0` is
irrelevant.) Used in part (a). -/
def row (μ : Partition) (i : ℕ) : ℕ := μ.parts.getD (i - 1) 0

/-- **Setting, "Partial sums"** of `q_chain_lemma.md`:
`S_t(μ) := μ_1 + ⋯ + μ_t`, padded with zeros. Used in parts (a) and (b). -/
def S (t : ℕ) (μ : Partition) : ℕ := ∑ i ∈ Finset.Icc 1 t, μ.row i

end Partition

open Partition

/-- **Setting, "Weak dominance"** of `q_chain_lemma.md`: `λ ≼ μ` iff `S_t(λ) ≤ S_t(μ)` for every
`t ≥ 1`. Used in parts (b) and (c). -/
def WeakDom (lam μ : Partition) : Prop := ∀ t, 1 ≤ t → S t lam ≤ S t μ

@[inherit_doc] infix:50 " ≼ " => WeakDom

/-- Re-sorting a list of naturals into weakly decreasing order (used in **Setting, "The options
of `μ`"** of `q_chain_lemma.md`, where the new rows are "re-sorted"); used in parts (a)–(c). -/
def sortDesc (l : List ℕ) : List ℕ := l.mergeSort (fun a b => decide (b ≤ a))

/-- Re-sorting yields a weakly decreasing list (used in parts (a)–(c) of `q_chain_lemma.md`). -/
lemma sortDesc_sorted (l : List ℕ) : (sortDesc l).Pairwise (· ≥ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (b ≤ a))
    (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) l
  simpa using this

/-- Re-sorting does not change membership (used in parts (a)–(c) of `q_chain_lemma.md`). -/
lemma mem_sortDesc {l : List ℕ} {x : ℕ} : x ∈ sortDesc l ↔ x ∈ l :=
  (List.mergeSort_perm l _).mem_iff

namespace Partition

/-- **Setting, "The options of `μ`"** of `q_chain_lemma.md`: `μ − e_j`, obtained from `μ` by
lowering row `j` by one and re-sorting, dropping a part that becomes `0`. (Row `j` is the entry at
index `j - 1` of the list.) Used in parts (a)–(c). -/
def subE (μ : Partition) (j : ℕ) : Partition where
  parts := sortDesc ((μ.parts.modify (j - 1) (· - 1)).filter (· ≠ 0))
  sorted := sortDesc_sorted _
  pos := by
    intro x hx
    rw [mem_sortDesc, List.mem_filter] at hx
    simp at hx
    omega

/-- **Setting, "The options of `μ`"** of `q_chain_lemma.md`: `μ + e_j`, obtained from `μ` by
raising row `j` by one and re-sorting. (Row `j` is the entry at index `j - 1` of the list.) Used in parts (a)–(c). -/
def addE (μ : Partition) (j : ℕ) : Partition where
  parts := sortDesc (μ.parts.modify (j - 1) (· + 1))
  sorted := sortDesc_sorted _
  pos := by
    intro x hx
    rw [mem_sortDesc] at hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.getElem_modify]
    split_ifs
    · omega
    · exact μ.pos _ (List.getElem_mem _)

/-- **Setting, "The options of `μ`"** of `q_chain_lemma.md`: `μ ⊔ 1`, obtained by adding a new
part equal to `1` (placed as the last row, which keeps the rows weakly decreasing since all
parts are `≥ 1`). Used in parts (a)–(c). -/
def addOne (μ : Partition) : Partition where
  parts := μ.parts ++ [1]
  sorted := by
    rw [List.pairwise_append]
    refine ⟨μ.sorted, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    have := μ.pos a ha
    omega
  pos := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · exact μ.pos x h
    · omega

/-- **Setting, "The options of `μ`"** of `q_chain_lemma.md`: `r̄_j := max{i : μ_i = μ_j}`, the
last row with the same length as row `j` (rows `i` range over `i ≥ 1`). Used in part (a). -/
noncomputable def rbar (μ : Partition) (j : ℕ) : ℕ := sSup {i | 1 ≤ i ∧ μ.row i = μ.row j}

/-- **Setting, "The options of `μ`"** of `q_chain_lemma.md`: `r̲_j := min{i : μ_i = μ_j}`, the
first row with the same length as row `j` (rows `i` range over `i ≥ 1`). Used in part (a). -/
noncomputable def rlow (μ : Partition) (j : ℕ) : ℕ := sInf {i | 1 ≤ i ∧ μ.row i = μ.row j}

/-- **Setting, "The list of options"** of `q_chain_lemma.md`: for a fixed integer `L ≥ 2ℓ`
and `p = 1, …, L`,
* `opt_p(μ) := μ − e_p` for `1 ≤ p ≤ ℓ`;
* `opt_p(μ) := μ ⊔ 1` for `ℓ < p ≤ L − ℓ`;
* `opt_p(μ) := μ + e_{L+1−p}` for `L − ℓ < p ≤ L`.

(The values at `p = 0` or `p > L` are irrelevant; the hypothesis `L ≥ 2ℓ` is carried by the
theorems.) Used in parts (b) and (c). -/
def opt (μ : Partition) (L p : ℕ) : Partition :=
  if p ≤ μ.len then μ.subE p
  else if p ≤ L - μ.len then μ.addOne
  else μ.addE (L + 1 - p)

end Partition

/-- **Setting, "down-set"** of `q_chain_lemma.md`: a set `Λ` of partitions is a down-set if
`λ ≼ μ` and `μ ∈ Λ` imply `λ ∈ Λ`. Used in part (c). -/
def IsDownSet (Λ : Set Partition) : Prop := ∀ lam μ, lam ≼ μ → μ ∈ Λ → lam ∈ Λ

end ChainLemma
