module

public import RequestProject.Chain.Main

/-!
# Definitions for `q_P2_monotone_options.md`

`q_P2_monotone_options.md` "uses the **Setting** of `q_chain_lemma.md` unchanged", so all its
notions (`Partition`, `S`, `≼` (`WeakDom`), `μ − e_j` (`subE`), `μ + e_j` (`addE`), `μ ⊔ 1`
(`addOne`), `r̄_j` (`rbar`), `r̲_j` (`rlow`), `opt_p(μ)` (`opt`) and `IsDownSet`) are reused from
`RequestProject/Chain/Defs.lean`. The only new notion is the size `|μ|`.
-/

@[expose] public section

namespace ChainLemma

namespace Partition

/-- Opening paragraph of `q_P2_monotone_options.md`: "Write `|μ| := μ_1 + ⋯ + μ_ℓ`", the size
(sum of the parts) of the partition `μ`. Used in the **Proposition** and the **Corollary**. -/
def size (μ : Partition) : ℕ := μ.parts.sum

end Partition

end ChainLemma
