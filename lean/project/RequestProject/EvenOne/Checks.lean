module

public import RequestProject.EvenCount.Defs

/-!
# Checks at the end of `q_even_block_one.md` (the numerical values only)

The file lists the values `QkEven j q` of the block counts (`1, 1, 1, 3, 19, 141, 7, 127` for
`q = 2, 4, 8`) and the values `Q_k(m)` of the colour-reduction sum
(`19, 141, 61, 61, 127, 217, 217, 331, 331` for `(m, k) = (4,1), (4,2), (6,1), (6,1), (8,1),
(10,1), (10,1), (12,1), (12,1)`; every `m` there is even, so `Q_k(m) = EvenCount.QkEven k m`).
Here these values are checked by `decide` (kernel evaluation, no `native_decide`), together with the
control «count at the wrong box `QkEven j (2q)`». The dimension computations in the literal ring
`F_2[t]/(t^q − 1)` and the checks of `θ` are not reproduced here; they are replaced by the theorems
of Parts B–E.
-/

@[expose] public section

namespace EvenOne

set_option maxRecDepth 100000

/-- **Checks** of `q_even_block_one.md`: `QkEven j 2 = 1` for `j = 0, 1, 2`. -/
theorem check_QkEven_two :
    EvenCount.QkEven 0 2 = 1 ∧ EvenCount.QkEven 1 2 = 1 ∧ EvenCount.QkEven 2 2 = 1 := by
  decide

/-- **Checks** of `q_even_block_one.md`: `QkEven j 4 = 3, 19, 141` for `j = 0, 1, 2` (also the
cells `(m, k) = (4, 1)`, `(4, 2)` of the colour-reduction sum). -/
theorem check_QkEven_four :
    EvenCount.QkEven 0 4 = 3 ∧ EvenCount.QkEven 1 4 = 19 ∧ EvenCount.QkEven 2 4 = 141 := by
  decide

/-- **Checks** of `q_even_block_one.md`: `QkEven j 8 = 7, 127` for `j = 0, 1` (also the cell
`(m, k) = (8, 1)`). -/
theorem check_QkEven_eight : EvenCount.QkEven 0 8 = 7 ∧ EvenCount.QkEven 1 8 = 127 := by
  decide

/-- **Checks** of `q_even_block_one.md`: the cells `(m, k) = (6, 1)`, `(10, 1)`, `(12, 1)` of the
colour-reduction sum: `Q_1(6) = 61`, `Q_1(10) = 217`, `Q_1(12) = 331`. -/
theorem check_QkEven_cells :
    EvenCount.QkEven 1 6 = 61 ∧ EvenCount.QkEven 1 10 = 217 ∧ EvenCount.QkEven 1 12 = 331 := by
  decide

/-- **Checks** of `q_even_block_one.md` (control «the count at the wrong box `QkEven j (2q)`»):
`QkEven 1 (2·2) ≠ QkEven 1 2` and `QkEven 1 (2·4) ≠ QkEven 1 4`. -/
theorem check_control_wrong_box :
    EvenCount.QkEven 1 (2 * 2) ≠ EvenCount.QkEven 1 2 ∧
      EvenCount.QkEven 1 (2 * 4) ≠ EvenCount.QkEven 1 4 := by
  decide

end EvenOne

end
