module

public import RequestProject.ColAssembly.EveryField
public import RequestProject.EvenBlocks.Part0

/-!
# Part 0, (02) of `q_even_blocks.md`: settings for every prime

`EvenBlocks.algClosureSetting`, `EvenBlocks.exists_setting`: for every prime `p`, `v ≥ 1`,
`r ≥ 1` with `p ∤ r` (no parity hypothesis on `p` or `r`), a Setting of `q_col_splitting.md` on
`AlgebraicClosure (ZMod p)` with `μ` the `r`-th roots of unity.
-/

@[expose] public section

namespace EvenBlocks

open ColSplit Polynomial

section Setting02

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Part 0, (02)** of `q_even_blocks.md`: for a prime `p`, `v ≥ 1` and `r ≥ 1` with `p ∤ r`, the
Setting on `K = AlgebraicClosure (ZMod p)` with `S.p = p`, `S.v = v`, `S.r = r` and
`S.μ = nthRootsFinset r 1` (built as the `let S` inside
`ColAssembly.finrank_IK_of_isAlgClosed_of_dvd`, with
`ColAssembly.prod_nthRootsFinset_of_isAlgClosed`; no parity of `p` or `r` is assumed). -/
noncomputable def algClosureSetting (v : ℕ) (hv : 1 ≤ v) (r : ℕ) (hr : 1 ≤ r) (hpr : ¬ p ∣ r) :
    ColSetting (AlgebraicClosure (ZMod p)) :=
  have hrK : (r : AlgebraicClosure (ZMod p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
    exact hpr
  { p := p, hp := hp.out, charP := inferInstance, v := v, one_le_v := hv, r := r,
    one_le_r := hr, μ := nthRootsFinset r (1 : AlgebraicClosure (ZMod p)),
    card_μ := (ColAssembly.prod_nthRootsFinset_of_isAlgClosed _ hr hrK).2,
    X_pow_sub_one := (ColAssembly.prod_nthRootsFinset_of_isAlgClosed _ hr hrK).1 }

/-- **Part 0, (02)** of `q_even_blocks.md`: for every prime `p`, every `v ≥ 1` and every `r ≥ 1`
with `¬ p ∣ r` (any parity of `p` and `r`), there is `S : ColSetting K`,
`K = AlgebraicClosure (ZMod p)`, with `S.p = p`, `S.v = v`, `S.r = r`,
`S.μ = nthRootsFinset r 1`; hence `S.m = p^v·r`. -/
theorem exists_setting (v : ℕ) (hv : 1 ≤ v) (r : ℕ) (hr : 1 ≤ r) (hpr : ¬ p ∣ r) :
    ∃ S : ColSetting (AlgebraicClosure (ZMod p)), S.p = p ∧ S.v = v ∧ S.r = r ∧
      S.μ = nthRootsFinset r (1 : AlgebraicClosure (ZMod p)) ∧ S.m = p ^ v * r :=
  ⟨algClosureSetting p v hv r hr hpr, rfl, rfl, rfl, rfl, rfl⟩

end Setting02

end EvenBlocks

end
