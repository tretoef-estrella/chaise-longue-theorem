module

public import RequestProject.EvenAll.PartBC
public import RequestProject.EvenAll.PartE

/-!
# Checks at the end of `q_even_assembly.md`

The numerical values listed in the checks are evaluated by `decide` (kernel evaluation, no
`native_decide`) and combined with the theorems of Parts B, C and E:

* the six even cells `(m, k) = (4,1), (4,2), (6,1), (8,1), (10,1), (12,1)`: the dimension of
  `I_F` and of the quotient, for **every** field `F` (so in particular at the primes `2, 3, 5`);
* the odd values `Qall m k = 6, 36, 90, 168, 20` at `(3,1), (5,1), (7,1), (9,1), (3,2)`;
* Corollary 9.12 (ii) over `AlgebraicClosure (ZMod 2)`: `dim Ibal a`, `dim Iph a` at `q = 2`
  (`a ≤ 3`) and at `q = 4` (`a ≤ 2` for `Iph`, `a ≤ 3` for `Ibal`);
* the controls «odd formula at `m ± 1`» and «`Nbal` at the wrong `q`».

Not reproduced: `dim Iph 3 = 2716` at `q = 4` (the kernel evaluation of `Nbal 4 4` is too slow),
the control «`Ibal` with exponent `q − 2`», and the computations in the literal rings `F_p[G]`
(they are replaced by the theorems).
-/

@[expose] public section

namespace EvenAll

open ColSplit ColUpper ColAssembly EvenCount

set_option maxRecDepth 100000

/-- **Checks** of `q_even_assembly.md`: the values `QkEven k m = 19, 141, 61, 127, 217, 331` at
the six even cells. -/
theorem check_QkEven_cells :
    QkEven 1 4 = 19 ∧ QkEven 2 4 = 141 ∧ QkEven 1 6 = 61 ∧ QkEven 1 8 = 127 ∧
      QkEven 1 10 = 217 ∧ QkEven 1 12 = 331 := by
  decide

/-- **Checks** of `q_even_assembly.md`, first item, through (B1)/(B2): for every field `F` (so at
the primes `2, 3, 5`), `dim_F I_F = 19` and `dim_F F[G]/I_F = 4^3 − 19 = 45` at `(m, k) = (4, 1)`. -/
theorem check_cell_4_1 (F : Type*) [Field F] :
    Module.finrank F ((IK F 4 1).restrictScalars F) = 19 ∧
      Module.finrank F (GA F (2 * 1 + 1) 4 ⧸ IK F 4 1) = 45 := by
  have h := check_QkEven_cells.1
  refine ⟨by rw [(B1 F (by norm_num : Even 4) (by norm_num) 1).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 4) (by norm_num) 1).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, first item: at `(m, k) = (4, 2)`, `dim_F I_F = 141` and
`dim_F F[G]/I_F = 4^5 − 141 = 883` for every field `F`. -/
theorem check_cell_4_2 (F : Type*) [Field F] :
    Module.finrank F ((IK F 4 2).restrictScalars F) = 141 ∧
      Module.finrank F (GA F (2 * 2 + 1) 4 ⧸ IK F 4 2) = 883 := by
  have h := check_QkEven_cells.2.1
  refine ⟨by rw [(B1 F (by norm_num : Even 4) (by norm_num) 2).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 4) (by norm_num) 2).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, first item: at `(m, k) = (6, 1)`, `dim_F I_F = 61` and
`dim_F F[G]/I_F = 6^3 − 61 = 155` for every field `F`. -/
theorem check_cell_6_1 (F : Type*) [Field F] :
    Module.finrank F ((IK F 6 1).restrictScalars F) = 61 ∧
      Module.finrank F (GA F (2 * 1 + 1) 6 ⧸ IK F 6 1) = 155 := by
  have h := check_QkEven_cells.2.2.1
  refine ⟨by rw [(B1 F (by norm_num : Even 6) (by norm_num) 1).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 6) (by norm_num) 1).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, first item: at `(m, k) = (8, 1)`, `dim_F I_F = 127` and
`dim_F F[G]/I_F = 8^3 − 127 = 385` for every field `F`. -/
theorem check_cell_8_1 (F : Type*) [Field F] :
    Module.finrank F ((IK F 8 1).restrictScalars F) = 127 ∧
      Module.finrank F (GA F (2 * 1 + 1) 8 ⧸ IK F 8 1) = 385 := by
  have h := check_QkEven_cells.2.2.2.1
  refine ⟨by rw [(B1 F (by norm_num : Even 8) (by norm_num) 1).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 8) (by norm_num) 1).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, first item: at `(m, k) = (10, 1)`, `dim_F I_F = 217` and
`dim_F F[G]/I_F = 10^3 − 217 = 783` for every field `F`. -/
theorem check_cell_10_1 (F : Type*) [Field F] :
    Module.finrank F ((IK F 10 1).restrictScalars F) = 217 ∧
      Module.finrank F (GA F (2 * 1 + 1) 10 ⧸ IK F 10 1) = 783 := by
  have h := check_QkEven_cells.2.2.2.2.1
  refine ⟨by rw [(B1 F (by norm_num : Even 10) (by norm_num) 1).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 10) (by norm_num) 1).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, first item: at `(m, k) = (12, 1)`, `dim_F I_F = 331` and
`dim_F F[G]/I_F = 12^3 − 331 = 1397` for every field `F`. -/
theorem check_cell_12_1 (F : Type*) [Field F] :
    Module.finrank F ((IK F 12 1).restrictScalars F) = 331 ∧
      Module.finrank F (GA F (2 * 1 + 1) 12 ⧸ IK F 12 1) = 1397 := by
  have h := check_QkEven_cells.2.2.2.2.2
  refine ⟨by rw [(B1 F (by norm_num : Even 12) (by norm_num) 1).2, h], ?_⟩
  rw [(B2 (by norm_num : Even 12) (by norm_num) 1).2 F, h]
  norm_num

/-- **Checks** of `q_even_assembly.md`, second item (odd `m`): `Qall m k = 6, 36, 90, 168, 20` at
`(m, k) = (3,1), (5,1), (7,1), (9,1), (3,2)`. -/
theorem check_Qall_odd :
    Qall 3 1 = 6 ∧ Qall 5 1 = 36 ∧ Qall 7 1 = 90 ∧ Qall 9 1 = 168 ∧ Qall 3 2 = 20 := by
  unfold Qall
  decide

/-- **Checks** of `q_even_assembly.md` (control «the odd formula at `m ± 1` differs from
`QkEven k m`»), at the six even cells. -/
theorem check_control_odd_formula :
    TheoremB.Qk 1 3 ≠ QkEven 1 4 ∧ TheoremB.Qk 1 5 ≠ QkEven 1 4 ∧
      TheoremB.Qk 1 5 ≠ QkEven 1 6 ∧ TheoremB.Qk 1 7 ≠ QkEven 1 6 ∧
      TheoremB.Qk 1 7 ≠ QkEven 1 8 ∧ TheoremB.Qk 1 9 ≠ QkEven 1 8 := by
  decide

set_option maxHeartbeats 2000000 in
/-- **Checks** of `q_even_assembly.md`, third item (the counts): at `q = 2`,
`Nbal a 2 = 1, 2, 6, 20` and `Nph a 2 = 2, 6, 20, 70` for `a = 0, 1, 2, 3`; at `q = 4`,
`Nbal a 4 = 1, 4, 28, 256` for `a = 0, 1, 2, 3` and `Nph a 4 = 4, 28, 256` for `a = 0, 1, 2`. -/
theorem check_counts :
    (Bip.Nbal 0 2 = 1 ∧ Bip.Nbal 1 2 = 2 ∧ Bip.Nbal 2 2 = 6 ∧ Bip.Nbal 3 2 = 20) ∧
    (Bip.Nph 0 2 = 2 ∧ Bip.Nph 1 2 = 6 ∧ Bip.Nph 2 2 = 20 ∧ Bip.Nph 3 2 = 70) ∧
    (Bip.Nbal 0 4 = 1 ∧ Bip.Nbal 1 4 = 4 ∧ Bip.Nbal 2 4 = 28 ∧ Bip.Nbal 3 4 = 256) ∧
    (Bip.Nph 0 4 = 4 ∧ Bip.Nph 1 4 = 28 ∧ Bip.Nph 2 4 = 256) := by
  simp only [Bip.lemma72_iii]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide

/-- **Checks** of `q_even_assembly.md` (control «`Nbal` at the wrong `q` differs»):
`Nbal a 2 ≠ Nbal a 4` for `a = 1, 2, 3`. -/
theorem check_control_wrong_q :
    Bip.Nbal 1 2 ≠ Bip.Nbal 1 4 ∧ Bip.Nbal 2 2 ≠ Bip.Nbal 2 4 ∧ Bip.Nbal 3 2 ≠ Bip.Nbal 3 4 := by
  decide

/-- **Checks** of `q_even_assembly.md`, third item, through (E1): over
`K = AlgebraicClosure (ZMod 2)` at `q = 2`, `dim Ibal a = 1, 2, 6, 20` and
`dim Iph a = 2, 6, 20, 70` for `a = 0, 1, 2, 3`. -/
theorem check_E1_q2 :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (∀ a,
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Ibal (AlgebraicClosure (ZMod 2)) 2 a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nbal a 2 ∧
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Iph (AlgebraicClosure (ZMod 2)) 2 a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nph a 2) ∧
    [Bip.Nbal 0 2, Bip.Nbal 1 2, Bip.Nbal 2 2, Bip.Nbal 3 2] = [1, 2, 6, 20] ∧
    [Bip.Nph 0 2, Bip.Nph 1 2, Bip.Nph 2 2, Bip.Nph 3 2] = [2, 6, 20, 70] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩, -, -⟩ := check_counts
  exact ⟨fun a => E1 (v := 1) le_rfl a, by rw [h1, h2, h3, h4], by rw [h5, h6, h7, h8]⟩

/-- **Checks** of `q_even_assembly.md`, third item, through (E1): over
`K = AlgebraicClosure (ZMod 2)` at `q = 4`, `dim Ibal a = 1, 4, 28, 256` for `a = 0, 1, 2, 3`
and `dim Iph a = 4, 28, 256` for `a = 0, 1, 2`. -/
theorem check_E1_q4 :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (∀ a,
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Ibal (AlgebraicClosure (ZMod 2)) 4 a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nbal a 4 ∧
      Module.finrank (AlgebraicClosure (ZMod 2))
        ((Bip.Iph (AlgebraicClosure (ZMod 2)) 4 a).restrictScalars
          (AlgebraicClosure (ZMod 2))) = Bip.Nph a 4) ∧
    [Bip.Nbal 0 4, Bip.Nbal 1 4, Bip.Nbal 2 4, Bip.Nbal 3 4] = [1, 4, 28, 256] ∧
    [Bip.Nph 0 4, Bip.Nph 1 4, Bip.Nph 2 4] = [4, 28, 256] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩⟩ := check_counts
  exact ⟨fun a => E1 (v := 2) (by norm_num) a, by rw [h1, h2, h3, h4], by rw [h5, h6, h7]⟩

end EvenAll

end
