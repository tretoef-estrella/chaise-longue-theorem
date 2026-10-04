module

public import RequestProject.EvenAll.PartA

/-!
# Parts B and C of `q_even_assembly.md`: Main Theorem′ for every even degree (Theorem 9.11) and
for every degree `m ≥ 1`

* **(B1)** `EvenAll.B1`: every field, even `m ≥ 2`.
* **(B2)** `EvenAll.B2`: Main Theorem′ for every even `m ≥ 2` (paper v11 Theorem 9.11).
* **(C1)** `EvenAll.Qall`; **(C2)** `EvenAll.mainTheorem'`: Main Theorem′ for every `m ≥ 1`.
-/

@[expose] public section

namespace EvenAll

open ColSplit ColUpper ColAssembly EvenCount

set_option synthInstance.maxHeartbeats 200000

/-- **Part B, (B1)** of `q_even_assembly.md` (**every field**): for every even `m ≥ 2`, every `k`
and every field `F` (in any universe), `rankOver F (intMatU m k) = QkEven k m` and
`finrank F ((IK F m k).restrictScalars F) = QkEven k m`. (`EvenAssembly.theorem_ii` with (A3).) -/
theorem B1 (F : Type*) [Field F] {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = QkEven k m ∧
      Module.finrank F ((IK F m k).restrictScalars F) = QkEven k m :=
  EvenAssembly.theorem_ii F heven h2 (A3 heven h2 k)

/-- **Part B, (B2)** of `q_even_assembly.md` (**Main Theorem′, even `m`**; paper v11
Theorem 9.11): for every even `m ≥ 2` and every `k`, `RZ (2k+1) m ⧸ IZ m k` is a free `ℤ`-module
of rank `m^{2k+1} − QkEven k m`, and for every field `F` (in any universe),
`finrank F (GA F (2k+1) m ⧸ IK F m k) = m^{2k+1} − QkEven k m`.
(`EvenAssembly.theorem_iii` with (A3).) -/
theorem B2 {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - QkEven k m) ∧
    ∀ (F : Type*) [Field F],
      Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - QkEven k m :=
  EvenAssembly.theorem_iii heven h2 (A3 heven h2 k)

/-- **Part C, (C1)** of `q_even_assembly.md`: the unified count
`Qall m k := if Even m then EvenCount.QkEven k m else TheoremB.Qk k m`. -/
noncomputable def Qall (m k : ℕ) : ℕ := if Even m then QkEven k m else TheoremB.Qk k m

/-- **Part C, (C2)** of `q_even_assembly.md` (**Main Theorem′ for every `m ≥ 1`**): for every
`m ≥ 1` and every `k`, `RZ (2k+1) m ⧸ IZ m k` is a free `ℤ`-module of rank
`m^{2k+1} − Qall m k`, and for every field `F` (in any universe),
`finrank F (GA F (2k+1) m ⧸ IK F m k) = m^{2k+1} − Qall m k` and
`finrank F ((IK F m k).restrictScalars F) = Qall m k`.
(Odd `m`: `ColAssembly.mainTheorem'_Z`, `mainTheorem'_field`, `finrank_IK_eq`; even `m`: (B2),
(B1).) -/
theorem mainTheorem' {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (Module.Free ℤ (RZ (2 * k + 1) m ⧸ IZ m k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) m ⧸ IZ m k) = m ^ (2 * k + 1) - Qall m k) ∧
    ∀ (F : Type*) [Field F],
      Module.finrank F (GA F (2 * k + 1) m ⧸ IK F m k) = m ^ (2 * k + 1) - Qall m k ∧
        Module.finrank F ((IK F m k).restrictScalars F) = Qall m k := by
  by_cases heven : Even m
  · have h2 : 2 ≤ m := by
      obtain ⟨t, ht⟩ := heven
      omega
    unfold Qall; rw [if_pos heven]
    exact ⟨(B2.{0} heven h2 k).1, fun F _ => ⟨(B2 heven h2 k).2 F, (B1 F heven h2 k).2⟩⟩
  · have hodd : Odd m := Nat.not_even_iff_odd.1 heven
    unfold Qall; rw [if_neg heven]
    exact ⟨ColAssembly.mainTheorem'_Z hodd k, fun F _ =>
      ⟨ColAssembly.mainTheorem'_field hodd k F, ColAssembly.finrank_IK_eq F hodd k⟩⟩

end EvenAll

end
