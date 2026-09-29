module

public import RequestProject.Chain.Main

/-!
# The checks of `q_chain_lemma.md`

Kernel-checked versions of the examples in the **Checks** section of `q_chain_lemma.md`.
-/

@[expose] public section

namespace ChainLemma

open Partition

/-- Re-sorting by merge sort agrees with insertion sort (used to evaluate the examples of the
**Checks** section of `q_chain_lemma.md`, illustrating part (b), in the kernel). -/
lemma sortDesc_eq_insertionSort (l : List ℕ) : sortDesc l = l.insertionSort (fun a b => b ≤ a) :=
  List.mergeSort_eq_insertionSort (fun a b : ℕ => b ≤ a) l

/-- The partition `μ = (2, 2, 1)` used in the **Checks** section of `q_chain_lemma.md` (examples for parts (a) and (b)). -/
def mu221 : Partition := ⟨[2, 2, 1], by decide, by decide⟩

/-- **Checks** of `q_chain_lemma.md` (the rows `r̄_j`, `r̲_j` of part (a)): for `μ = (2, 2, 1)`: `r̄_1 = r̄_2 = 2`, `r̄_3 = 3`,
`r̲_1 = r̲_2 = 1`, `r̲_3 = 3`. -/
theorem check_rows :
    mu221.rbar 1 = 2 ∧ mu221.rbar 2 = 2 ∧ mu221.rbar 3 = 3 ∧
    mu221.rlow 1 = 1 ∧ mu221.rlow 2 = 1 ∧ mu221.rlow 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (rw [rbar_eq _ _ (by decide) (by decide)]; decide)
  | (rw [rlow_eq _ _ (by decide) (by decide)]; decide)

/-- **Checks** of `q_chain_lemma.md` (illustrating part (b)): for `μ = (2, 2, 1)` and `L = 6`, the options in position
order are `(2,1,1), (2,1,1), (2,2), (2,2,2), (3,2,1), (3,2,1)`. -/
theorem check_opts_L6 :
    (List.range' 1 6).map (fun p => (mu221.opt 6 p).parts) =
      [[2, 1, 1], [2, 1, 1], [2, 2], [2, 2, 2], [3, 2, 1], [3, 2, 1]] := by
  simp [mu221, opt, subE, addE, addOne, len, List.range',
    sortDesc_eq_insertionSort]

/-- **Checks** of `q_chain_lemma.md` (illustrating part (b)): for `μ = (2, 2, 1)` and `L = 6`, the values
`(S_1, S_2, S_3)` of the options are `(2,3,4), (2,3,4), (2,4,4), (2,4,6), (3,5,6), (3,5,6)`. -/
theorem check_S_L6 :
    (List.range' 1 6).map (fun p => [S 1 (mu221.opt 6 p), S 2 (mu221.opt 6 p),
      S 3 (mu221.opt 6 p)]) =
      [[2, 3, 4], [2, 3, 4], [2, 4, 4], [2, 4, 6], [3, 5, 6], [3, 5, 6]] := by
  simp [S_eq_sum_take, mu221, opt, subE, addE, addOne, len, List.range',
    sortDesc_eq_insertionSort]

/-- **Checks** of `q_chain_lemma.md` (illustrating part (b)): for `μ = (2, 2, 1)` and `L = 8`, the same list with two
copies of `μ ⊔ 1 = (2,2,1,1)` inserted between `(2,2)` and `(2,2,2)`. -/
theorem check_opts_L8 :
    (List.range' 1 8).map (fun p => (mu221.opt 8 p).parts) =
      [[2, 1, 1], [2, 1, 1], [2, 2], [2, 2, 1, 1], [2, 2, 1, 1], [2, 2, 2], [3, 2, 1],
        [3, 2, 1]] := by
  simp [mu221, opt, subE, addE, addOne, len, List.range',
    sortDesc_eq_insertionSort]

/-- **Checks** of `q_chain_lemma.md` (illustrating part (b)): for `μ = ∅` and `L = 4`, every option is `(1)`. -/
theorem check_empty :
    (List.range' 1 4).map (fun p => ((⟨[], by decide, by decide⟩ : Partition).opt 4 p).parts) =
      [[1], [1], [1], [1]] := by
  decide +kernel

end ChainLemma
