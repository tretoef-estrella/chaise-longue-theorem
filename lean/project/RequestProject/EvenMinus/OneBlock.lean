module

public import RequestProject.EvenColours.Main
public import RequestProject.ColOne.Main
public import RequestProject.EvenBlocks.Main

/-!
# Part Q of `q_even_block_minus.md`: the block of colour `1` at an odd prime (Lemma 9.8)

(Q1) `EvenMinus.lemma98`: if `p ≠ 2`, then `NS S 1 |𝒞_1| ≤ dim_F I_{c,1}`, where
`I_{c,1} = EvenBlocks.IcS S c 1` (`= ColDecomp.Ic1 S c` by `rfl`). From `ColOne.lemma66_ii`
(`0 ∈ 𝒞_1`, `|𝒞_1| = 2j + 2`) with `EvenColours.C3_a` and `TheoremB.card_closedTuples`; from
`ColOne.lemma66_iii` (`0 ∉ 𝒞_1`, `|𝒞_1| = 2j`) with `EvenColours.C3_a`; and `EvenColours.C3_d`
for odd `|𝒞_1|`.
-/

@[expose] public section

namespace EvenMinus

open ColSplit ColSurv ColComp ColDecomp EvenBlocks EvenColours TheoremB

open scoped Classical

variable {F : Type*} [Field F] {S : ColSetting F} {k : ℕ}

/-- **Part Q, (Q1)** of `q_even_block_minus.md`: **Lemma 9.8**. If `S.p ≠ 2`, then for every
colouring `c`, `NS S 1 |𝒞_1| ≤ dim_F I_{c,1}` with `I_{c,1} = EvenBlocks.IcS S c 1`. -/
theorem lemma98 (hp : S.p ≠ 2) (c : Fin (2 * k + 1) → S.μ) :
    NS S 1 (cls (cExt c) 1).card ≤ Module.finrank F (IcS S c 1) := by
  rcases Nat.even_or_odd (cls (cExt c) 1).card with ⟨j, hj⟩ | hodd
  · by_cases h0 : (0 : Fin (2 * k + 2)) ∈ cls (cExt c) 1
    · have hpos : 0 < (cls (cExt c) 1).card := Finset.card_pos.2 ⟨_, h0⟩
      obtain ⟨j', hj'⟩ : ∃ j', (cls (cExt c) 1).card = 2 * j' + 2 := ⟨j - 1, by omega⟩
      rw [hj', C3_a S hp, card_closedTuples (q := S.q)]
      exact (ColOne.lemma66_ii S hp c h0 hj').2
    · have hj2 : (cls (cExt c) 1).card = 2 * j := by omega
      rw [hj2, C3_a S hp]
      exact ColOne.lemma66_iii S hp c h0 hj2
  · rw [C3_d S 1 hodd]
    exact Nat.zero_le _

end EvenMinus

end
