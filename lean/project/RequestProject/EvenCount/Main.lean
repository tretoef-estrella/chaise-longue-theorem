module

public import RequestProject.EvenCount.Number
public import RequestProject.EvenCount.Points
public import RequestProject.ColUpper.Main

/-!
# Part (vi) of the Theorem of `q_even_count.md`: the upper bound for even `m`

For `m ≥ 2` even and every field `F`: `dim_F I_F ≤ Q^e_k(m)`, with equality if `char F = 0` and
`F` contains `m` distinct `m`-th roots of unity; and `rank_ℚ(A) = Q^e_k(m)`.

As in the file (and as in `ColUpper.Main`), the proof goes through `ℂ`:
`dim_F I_F = rank_F(A) ≤ rank_ℚ(A) = rank_ℂ(A) = dim_ℂ I_ℂ = |Γ| = Q^e_k(m)`.
-/

@[expose] public section

namespace EvenCount

open ColSplit TheoremB ColUpper

set_option synthInstance.maxHeartbeats 200000

/-- **Proof of (vi)** in `q_even_count.md`: for `m ≥ 2` even, `dim_ℂ I_ℂ = |Γ| = Q^e_k(m)` (by
part (ii) of `q_col_upper.md` and (v) over `ℂ`). -/
theorem finrank_IK_complex_even {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) :
    Module.finrank ℂ ((IK ℂ m k).restrictScalars ℂ) = QkEven k m := by
  have hm : 0 < m := by omega
  rw [finrank_IK_eq_card_Gamma (prod_rootsC hm) k,
    card_Gamma_even (prod_rootsC hm) (Nat.cast_ne_zero.2 hm.ne') heven k]

/-- **Theorem (vi)** of `q_even_count.md`, last claim: for `m ≥ 2` even,
`rank_ℚ(A) = Q^e_k(m)`, where `A = intMatU m k` is the integer matrix of part (i) of
`q_col_upper.md`. -/
theorem rankOver_rat_intMatU_even {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) :
    EveryField.rankOver ℚ (intMatU m k) = QkEven k m := by
  rw [← EveryField.rankOver_eq_rankOver_rat ℂ, ← finrank_IK_eq_rankOver (by omega),
    finrank_IK_complex_even heven h2]

/-- **Theorem (vi)** of `q_even_count.md` (the upper bound for even `m`): for `m ≥ 2` even and
every field `F`, `dim_F I_F ≤ Q^e_k(m)`. -/
theorem finrank_IK_le_even (F : Type*) [Field F] {m : ℕ} (heven : Even m) (h2 : 2 ≤ m)
    (k : ℕ) :
    Module.finrank F ((IK F m k).restrictScalars F) ≤ QkEven k m := by
  rw [finrank_IK_eq_rankOver (by omega)]
  exact (EveryField.rankOver_le_rankOver_rat F _).trans
    (rankOver_rat_intMatU_even heven h2 k).le

/-- **Theorem (vi)** of `q_even_count.md` (equality case): for `m ≥ 2` even, if `char F = 0` and
`F` contains a set `μ_m` of `m` distinct `m`-th roots of unity
(`X^m − 1 = Π_{ξ ∈ μ_m} (X − ξ)`), then `dim_F I_F = Q^e_k(m)` (by part (ii) of
`q_col_upper.md` and (v) directly, as `m ≠ 0` in `F`). The hypothesis `|μ_m| = m` follows from
the factorization and is omitted. -/
theorem finrank_IK_eq_of_charZero_even (F : Type*) [Field F] [CharZero F] {m : ℕ}
    (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) {μm : Finset F}
    (hprod : (Polynomial.X ^ m - 1 : Polynomial F) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ)) :
    Module.finrank F ((IK F m k).restrictScalars F) = QkEven k m := by
  rw [finrank_IK_eq_card_Gamma hprod k,
    card_Gamma_even hprod (Nat.cast_ne_zero.2 (by omega)) heven k]

/-- **Theorem (vi)** of `q_even_count.md` (the upper bound for even `m`), all claims together,
in the form of `ColUpper.theorem_iv`: let `m ≥ 2` be even. Then for every field `F`,
`dim_F I_F ≤ Q^e_k(m)`; equality holds if `char F = 0` and `F` contains `m` distinct `m`-th roots
of unity (`|μ_m| = m` and `X^m − 1 = Π_{ξ ∈ μ_m} (X − ξ)`); and `rank_ℚ(A) = Q^e_k(m)` for the
integer matrix `A = intMatU m k` of part (i) of `q_col_upper.md`. -/
theorem theorem_iv_even {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (k : ℕ) :
    (∀ (F : Type) [Field F], Module.finrank F ((IK F m k).restrictScalars F) ≤ QkEven k m) ∧
    (∀ (F : Type) [Field F] [CharZero F] (μm : Finset F), μm.card = m →
      (Polynomial.X ^ m - 1 : Polynomial F) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ) →
      Module.finrank F ((IK F m k).restrictScalars F) = QkEven k m) ∧
    EveryField.rankOver ℚ (intMatU m k) = QkEven k m :=
  ⟨fun F _ => finrank_IK_le_even F heven h2 k,
    fun F _ _ _ _ hprod => finrank_IK_eq_of_charZero_even F heven h2 k hprod,
    rankOver_rat_intMatU_even heven h2 k⟩

end EvenCount

end
