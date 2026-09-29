module

public import RequestProject.TheoremB.Defs

/-!
# Checks of `q_theorem_B_lower.md`: values of `Q_k(q)`

The values of `Q_k(q)` listed in the **Checks** section of `q_theorem_B_lower.md`, evaluated from
the definition `Qk` (the linear-algebra computations of `dim (D_J)` over `F_101` and the
enumerations of `Γ'` are not reproduced; by parts (ii) and (iii) the latter two numbers equal
`Q_k(q)`).
-/

@[expose] public section

namespace TheoremB

/-- **Checks** of `q_theorem_B_lower.md`: `Q_k(q)` for
`(k, q) ∈ {(0,3), (0,5), (1,3), (1,5), (1,7), (2,3), (2,5), (3,3)}` is
`2, 4, 6, 36, 90, 20, 400, 70`. -/
theorem Qk_checks :
    Qk 0 3 = 2 ∧ Qk 0 5 = 4 ∧ Qk 1 3 = 6 ∧ Qk 1 5 = 36 ∧ Qk 1 7 = 90 ∧ Qk 2 3 = 20 ∧
      Qk 2 5 = 400 ∧ Qk 3 3 = 70 := by
  decide

/-- **Checks** of `q_theorem_B_lower.md` (table of the paper): `Q_1(9) = 168` and
`Q_2(5) = 400`. -/
theorem Qk_table : Qk 1 9 = 168 ∧ Qk 2 5 = 400 := by
  decide

/-- **Checks** of `q_theorem_B_lower.md` (table of the paper): `Q_k(3) = C(2k+2, k+1)`, checked
for `k = 0, …, 4`. -/
theorem Qk_three_small :
    ∀ k ∈ Finset.range 5, Qk k 3 = (2 * k + 2).choose (k + 1) := by
  decide

end TheoremB

end
