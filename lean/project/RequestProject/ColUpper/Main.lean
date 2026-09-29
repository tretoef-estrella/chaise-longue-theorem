module

public import RequestProject.ColUpper.Integral
public import RequestProject.ColUpper.Points

/-!
# Part (iv) of the Theorem of `q_col_upper.md`: the upper bound (6.1)

For `m ≥ 3` odd and every field `F`: `dim_F I_F ≤ Q_k(m)`, with equality if `char F = 0` and `F`
contains `m` distinct `m`-th roots of unity; in particular `rank_ℚ(A) = Q_k(m)`.

As in the file, the proof goes through `ℂ`: the `m`-th roots of unity `Polynomial.nthRootsFinset m 1`
in `ℂ` (the powers of `e^{2πi/m}`) satisfy `X^m − 1 = Π (X − ζ)`, and `m ≠ 0` in `ℂ`; so
`dim_F I_F = rank_F(A) ≤ rank_ℚ(A) = rank_ℂ(A) = dim_ℂ I_ℂ = |Γ| = Q_k(m)` by (i), (ii), (iii) and
part (ii) of `q_every_field.md` (`EveryField.rankOver_le_rankOver_rat`,
`EveryField.rankOver_eq_rankOver_rat`).
-/

@[expose] public section

namespace ColUpper

open ColSplit TheoremB

set_option synthInstance.maxHeartbeats 200000

/-- **Proof of (iv)** in `q_col_upper.md`: the set of `m`-th roots of unity in `ℂ`. -/
noncomputable def rootsC (m : ℕ) : Finset ℂ := Polynomial.nthRootsFinset m (1 : ℂ)

/-- **Proof of (iv)** in `q_col_upper.md`: for `m ≥ 1`, `ℂ` contains `m` distinct `m`-th roots of
unity: `X^m − 1 = Π_{ζ ∈ μ_m} (X − ζ)` in `ℂ[X]`, with `μ_m` the powers of `e^{2πi/m}`. -/
theorem prod_rootsC {m : ℕ} (hm : 0 < m) :
    (Polynomial.X ^ m - 1 : Polynomial ℂ) = ∏ ζ ∈ rootsC m, (Polynomial.X - Polynomial.C ζ) :=
  Polynomial.X_pow_sub_one_eq_prod hm (Complex.isPrimitiveRoot_exp m hm.ne')

/-- **Proof of (iv)** in `q_col_upper.md`: `|μ_m| = m` for the `m`-th roots of unity in `ℂ`. -/
theorem card_rootsC {m : ℕ} (hm : 0 < m) : (rootsC m).card = m :=
  (Complex.isPrimitiveRoot_exp m hm.ne').card_nthRootsFinset

/-- **Proof of (iv)** in `q_col_upper.md`: for `m ≥ 1` odd, `dim_ℂ I_ℂ = |Γ| = Q_k(m)` (by (ii)
and (iii) over `ℂ`). -/
theorem finrank_IK_complex {m : ℕ} (hodd : Odd m) (k : ℕ) :
    Module.finrank ℂ ((IK ℂ m k).restrictScalars ℂ) = Qk k m := by
  have hm : 0 < m := hodd.pos
  rw [finrank_IK_eq_card_Gamma (prod_rootsC hm) k,
    card_Gamma (prod_rootsC hm) (Nat.cast_ne_zero.2 hm.ne') hodd k]

/-- **Theorem (iv)** of `q_col_upper.md`, last claim: for `m ≥ 3` odd,
`rank_ℚ(A) = Q_k(m)`, where `A = intMatU m k` is the integer matrix of (i). (The proof works for
every odd `m ≥ 1`.) -/
theorem rankOver_rat_intMatU {m : ℕ} (hodd : Odd m) (k : ℕ) :
    EveryField.rankOver ℚ (intMatU m k) = Qk k m := by
  rw [← EveryField.rankOver_eq_rankOver_rat ℂ, ← finrank_IK_eq_rankOver hodd.pos,
    finrank_IK_complex hodd]

/-- **Theorem (iv)** of `q_col_upper.md` (the upper bound (6.1)): for `m ≥ 3` odd and every field
`F`, `dim_F I_F ≤ Q_k(m)`. (The proof works for every odd `m ≥ 1`.) -/
theorem finrank_IK_le (F : Type*) [Field F] {m : ℕ} (hodd : Odd m) (k : ℕ) :
    Module.finrank F ((IK F m k).restrictScalars F) ≤ Qk k m := by
  rw [finrank_IK_eq_rankOver hodd.pos]
  exact (EveryField.rankOver_le_rankOver_rat F _).trans (rankOver_rat_intMatU hodd k).le

/-- **Theorem (iv)** of `q_col_upper.md` (equality case): if `char F = 0` and `F` contains a set
`μ_m` of `m` distinct `m`-th roots of unity (`X^m − 1 = Π_{ξ ∈ μ_m} (X − ξ)`), then
`dim_F I_F = Q_k(m)` for `m` odd (by (ii) and (iii) directly, as `m ≠ 0` in `F`). The hypothesis
`|μ_m| = m` follows from the factorization (`card_of_prod`) and is omitted; the proof works for
every odd `m ≥ 1`. -/
theorem finrank_IK_eq_of_charZero (F : Type*) [Field F] [CharZero F] {m : ℕ} (hodd : Odd m)
    (k : ℕ) {μm : Finset F}
    (hprod : (Polynomial.X ^ m - 1 : Polynomial F) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ)) :
    Module.finrank F ((IK F m k).restrictScalars F) = Qk k m := by
  rw [finrank_IK_eq_card_Gamma hprod k,
    card_Gamma hprod (Nat.cast_ne_zero.2 hodd.pos.ne') hodd k]

/-- **Theorem (iv)** of `q_col_upper.md` (the upper bound (6.1)), all claims together: let
`m` be odd. Then for every field `F`, `dim_F I_F ≤ Q_k(m)`; equality holds if `char F = 0`
and `F` contains `m` distinct `m`-th roots of unity (`|μ_m| = m` and
`X^m − 1 = Π_{ξ ∈ μ_m} (X − ξ)`); and `rank_ℚ(A) = Q_k(m)` for the integer matrix
`A = intMatU m k` of (i). The file assumes `m ≥ 3`; this hypothesis is not needed by the proof
(for `m = 1` all three quantities are `0`), so the statement is slightly more general. -/
theorem theorem_iv {m : ℕ} (hodd : Odd m) (k : ℕ) :
    (∀ (F : Type) [Field F], Module.finrank F ((IK F m k).restrictScalars F) ≤ Qk k m) ∧
    (∀ (F : Type) [Field F] [CharZero F] (μm : Finset F), μm.card = m →
      (Polynomial.X ^ m - 1 : Polynomial F) = ∏ ξ ∈ μm, (Polynomial.X - Polynomial.C ξ) →
      Module.finrank F ((IK F m k).restrictScalars F) = Qk k m) ∧
    EveryField.rankOver ℚ (intMatU m k) = Qk k m :=
  ⟨fun F _ => finrank_IK_le F hodd k,
    fun F _ _ _ _ hprod => finrank_IK_eq_of_charZero F hodd k hprod,
    rankOver_rat_intMatU hodd k⟩

end ColUpper

end
