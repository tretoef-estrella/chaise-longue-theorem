module

public import RequestProject.EvenAssembly.Main
public import RequestProject.Pow2.Main

/-!
# Parts (iv) and (v) of the Theorem of `q_quartic_assembly.md`: the degree `4`

* **(iv)** `EvenAssembly.hypH_four`: `H(4, k)` holds for every `k`, from (vii) of
  `q_pow2_leading.md` (`Pow2.quartic_char_two`) with `F = ZMod 2`.
* **(v)** `EvenAssembly.mainTheorem'_four` and `EvenAssembly.every_field_four`: Main Theorem′ for
  the degree `4`.
-/

@[expose] public section

namespace EvenAssembly

open ColSplit ColUpper ColAssembly EvenCount

set_option synthInstance.maxHeartbeats 200000

/-- **Theorem (iv)** of `q_quartic_assembly.md` (`H` for the degree `4`): `H(4, k)` holds for every
`k`, i.e. `rank_{F_2}(A) = Q^e_k(4)`. The only prime dividing `4` is `2`, and by (vii) of
`q_pow2_leading.md`, `dim_{F_2} I_{F_2} = Q^e_k(4)`, which is `rank_{F_2}(A)` by (i) of
`q_col_upper.md`. -/
theorem hypH_four (k : ℕ) : HypH 4 k := by
  intro p hp hdvd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd))
  subst hp2
  rw [← finrank_IK_eq_rankOver (by norm_num)]
  exact Pow2.quartic_char_two (ZMod 2) k

/-- **Theorem (v)** of `q_quartic_assembly.md` (Main Theorem′ for the degree `4`), every-field part:
for every field `F` (in any universe) and every `k`, `rank_F(A) = Q^e_k(4)` and
`dim_F I_F = Q^e_k(4)`. By (iv) and (ii). -/
theorem every_field_four (F : Type*) [Field F] (k : ℕ) :
    EveryField.rankOver F (intMatU 4 k) = QkEven k 4 ∧
      Module.finrank F ((IK F 4 k).restrictScalars F) = QkEven k 4 :=
  theorem_ii F (by decide) (by norm_num) (hypH_four k)

/-- **Theorem (v)** of `q_quartic_assembly.md` (Main Theorem′ for the degree `4`), in the shape of
`ColAssembly.mainTheorem'`: for every `k`, `R/I_ℤ` is a free `ℤ`-module of rank
`4^{2k+1} − Q^e_k(4)`, and for every field `F`, `dim_F F[G]/I_F = 4^{2k+1} − Q^e_k(4)`. By (iv)
and (iii) with `m = 4`. (The statements `rank_F(A) = Q^e_k(4)` and `dim_F I_F = Q^e_k(4)` of (v)
are `every_field_four`.) -/
theorem mainTheorem'_four (k : ℕ) :
    (Module.Free ℤ (RZ (2 * k + 1) 4 ⧸ IZ 4 k) ∧
      Module.finrank ℤ (RZ (2 * k + 1) 4 ⧸ IZ 4 k) = 4 ^ (2 * k + 1) - QkEven k 4) ∧
    ∀ (F : Type) [Field F],
      Module.finrank F (GA F (2 * k + 1) 4 ⧸ IK F 4 k) = 4 ^ (2 * k + 1) - QkEven k 4 :=
  ⟨mainTheorem'_Z_even (by decide) (by norm_num) (hypH_four k),
    fun F _ => mainTheorem'_field_even (by decide) (by norm_num) (hypH_four k) F⟩

end EvenAssembly

end
