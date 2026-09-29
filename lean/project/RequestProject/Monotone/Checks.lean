module

public import RequestProject.Monotone.Main

/-!
# The parity remark of `q_P2_monotone_options.md`

Kernel-checked version of the remark after the **Corollary** of `q_P2_monotone_options.md`:
without the parity hypothesis the **Proposition** fails.
-/

@[expose] public section

namespace ChainLemma

open Partition

/-- Remark after the **Corollary** of `q_P2_monotone_options.md` ("Without the parity hypothesis
the statement is false"): for `h = 1` (so `L = 2`), `μ = ∅` and `μ̃ = (1)`, all hypotheses of the
**Proposition** hold except the parity condition `|μ| ≡ |μ̃| (mod 2)`, and at position `p = 1`,
`opt_1(μ) = (1)` is not `≼ opt_1(μ̃) = ∅`. -/
theorem parity_hypothesis_needed :
    let μ : Partition := ⟨[], by decide, by decide⟩
    let ν : Partition := ⟨[1], by decide, by decide⟩
    μ.len ≤ 1 ∧ ν.len ≤ 1 ∧ μ.size % 2 ≠ ν.size % 2 ∧ μ ≼ ν ∧
      ¬ (μ.opt (2 * 1) 1 ≼ ν.opt (2 * 1) 1) := by
  intro μ ν
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro t _
    simp [μ, S_eq_sum_take]
  · intro hle
    have := hle 1 le_rfl
    simp [μ, ν, opt, subE, addOne, len, S_eq_sum_take, sortDesc] at this

end ChainLemma
