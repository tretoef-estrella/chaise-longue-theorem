module

public import RequestProject.OddEquality.PartD

/-!
# Checks at the end of `q_oddbox_equality.md`

The numerical values of the checks are evaluated by `decide` (kernel evaluation, no
`native_decide`) and combined with (D1):

* the ten cells `(r, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,0), (7,1), (9,1), (11,1), (13,1)`:
  `N_r(2k+2) = Q^e_k(r+1) = 3, 19, 141, 5, 61, 7, 127, 217, 331, 469`, and, by (D1),
  `dim_F (D_J) = dim_F ℳ = N_r(2k+2)` for **every** field `F` (in particular `F_2, F_3, F_5, F_7`
  and `ℚ`);
* «the bound of Part B is attained»: `partB_attained` (in general, over `ℚ`);
* «the coefficient of `y_0^{r−1}` in `D(y_0, y_1)` is `1`»: `theta_D0` (in general);
* the control «the count at `r + 2` differs», in nine of the ten cells (the cell `(13, 1)` needs
  `Q^e_1(16)`, whose kernel evaluation is too slow, and is not reproduced).

Not reproduced: the two other controls (`D^−` in place of `D`, a point set without the zero), which
are computations in specific rings rather than consequences of the theorems.
-/

@[expose] public section

namespace OddEquality

open EvenCount

set_option maxRecDepth 100000

/-- **Checks** of `q_oddbox_equality.md`: `N_r(2k+2) = Q^e_k(r+1)` at the first nine cells
`(r, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,0), (7,1), (9,1), (11,1)`. -/
theorem check_values :
    QkEven 0 4 = 3 ∧ QkEven 1 4 = 19 ∧ QkEven 2 4 = 141 ∧ QkEven 0 6 = 5 ∧ QkEven 1 6 = 61 ∧
      QkEven 0 8 = 7 ∧ QkEven 1 8 = 127 ∧ QkEven 1 10 = 217 ∧ QkEven 1 12 = 331 := by
  decide

set_option maxHeartbeats 4000000 in
/-- **Checks** of `q_oddbox_equality.md`: `N_{13}(4) = Q^e_1(14) = 469` (cell `(r, k) = (13, 1)`). -/
theorem check_value_13_1 : QkEven 1 14 = 469 := by
  decide

/-- **Checks** of `q_oddbox_equality.md`, through (D1): for every field `F`, at the ten cells,
`dim_F (D_J) = N_r(2k+2)` (`TheoremB.DIdeal F (r+1) k`). -/
theorem check_DJ (F : Type*) [Field F] :
    Module.finrank F ((TheoremB.DIdeal F 4 0).restrictScalars F) = 3 ∧
      Module.finrank F ((TheoremB.DIdeal F 4 1).restrictScalars F) = 19 ∧
      Module.finrank F ((TheoremB.DIdeal F 4 2).restrictScalars F) = 141 ∧
      Module.finrank F ((TheoremB.DIdeal F 6 0).restrictScalars F) = 5 ∧
      Module.finrank F ((TheoremB.DIdeal F 6 1).restrictScalars F) = 61 ∧
      Module.finrank F ((TheoremB.DIdeal F 8 0).restrictScalars F) = 7 ∧
      Module.finrank F ((TheoremB.DIdeal F 8 1).restrictScalars F) = 127 ∧
      Module.finrank F ((TheoremB.DIdeal F 10 1).restrictScalars F) = 217 ∧
      Module.finrank F ((TheoremB.DIdeal F 12 1).restrictScalars F) = 331 ∧
      Module.finrank F ((TheoremB.DIdeal F 14 1).restrictScalars F) = 469 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := check_values
  exact ⟨(D1 F (h := 1) le_rfl 0).1.trans v1, (D1 F (h := 1) le_rfl 1).1.trans v2,
    (D1 F (h := 1) le_rfl 2).1.trans v3, (D1 F (h := 2) (by norm_num) 0).1.trans v4,
    (D1 F (h := 2) (by norm_num) 1).1.trans v5, (D1 F (h := 3) (by norm_num) 0).1.trans v6,
    (D1 F (h := 3) (by norm_num) 1).1.trans v7, (D1 F (h := 4) (by norm_num) 1).1.trans v8,
    (D1 F (h := 5) (by norm_num) 1).1.trans v9,
    (D1 F (h := 6) (by norm_num) 1).1.trans check_value_13_1⟩

/-- **Checks** of `q_oddbox_equality.md`, through (D1): for every field `F`, `dim_F ℳ = N_r(2k+2)`
at the cells `(r, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,0)` (`ℳ ⊆ Peel.C F (r+1) (2k+2)`). -/
theorem check_M (F : Type*) [Field F] :
    Module.finrank F ((Mideal F 4 2).restrictScalars F) = 3 ∧
      Module.finrank F ((Mideal F 4 4).restrictScalars F) = 19 ∧
      Module.finrank F ((Mideal F 4 6).restrictScalars F) = 141 ∧
      Module.finrank F ((Mideal F 6 2).restrictScalars F) = 5 ∧
      Module.finrank F ((Mideal F 6 4).restrictScalars F) = 61 ∧
      Module.finrank F ((Mideal F 8 2).restrictScalars F) = 7 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, -⟩ := check_values
  exact ⟨(D1 F (h := 1) le_rfl 0).2.trans v1, (D1 F (h := 1) le_rfl 1).2.trans v2,
    (D1 F (h := 1) le_rfl 2).2.trans v3, (D1 F (h := 2) (by norm_num) 0).2.trans v4,
    (D1 F (h := 2) (by norm_num) 1).2.trans v5, (D1 F (h := 3) (by norm_num) 0).2.trans v6⟩

/-- **Checks** of `q_oddbox_equality.md`, control «the count at `r + 2` differs»: `Q^e_k(r+3) ≠
Q^e_k(r+1)` at the cells `(r, k) = (3,0), (3,1), (3,2), (5,0), (5,1), (7,0), (7,1), (9,1), (11,1)`. -/
theorem check_control_r_plus_two :
    QkEven 0 6 ≠ QkEven 0 4 ∧ QkEven 1 6 ≠ QkEven 1 4 ∧ QkEven 2 6 ≠ QkEven 2 4 ∧
      QkEven 0 8 ≠ QkEven 0 6 ∧ QkEven 1 8 ≠ QkEven 1 6 ∧ QkEven 0 10 ≠ QkEven 0 8 ∧
      QkEven 1 10 ≠ QkEven 1 8 ∧ QkEven 1 12 ≠ QkEven 1 10 := by
  decide

/-- **Checks** of `q_oddbox_equality.md`, control «the count at `r + 2` differs», cell
`(r, k) = (11, 1)`: `Q^e_1(14) ≠ Q^e_1(12)`. -/
theorem check_control_11_1 : QkEven 1 14 ≠ QkEven 1 12 := by
  rw [check_value_13_1, check_values.2.2.2.2.2.2.2.2]
  decide

end OddEquality

end
