module

public import RequestProject.ColAssembly.EveryField
public import RequestProject.EvenCount.Main
public import RequestProject.EvenCount.Points

/-!
# Parts (i) and (ii) of the Theorem of `q_quartic_assembly.md`

For even `m ≥ 2`, `A = ColUpper.intMatU m k` is the integer matrix of `q_col_upper.md` and
`I_F = ColUpper.IK F m k`.

* `EvenAssembly.HypH m k` is the **Hypothesis `H(m, k)`** of the Setting.
* **(i)** `EvenAssembly.theorem_i`: if `m ≠ 0` in `F`, `rank_F(A) = Q^e_k(m) = dim_F I_F`.
* **(ii)** `EvenAssembly.theorem_ii`: under `H(m, k)`, the same for every field `F`.

This is the copy, for even `m` with `EvenCount.QkEven`, of `RequestProject/ColAssembly/EveryField.lean`;
the branch "`p ∣ m`" (Proposition 6.9) is replaced by the hypothesis `H(m, k)`.
-/

@[expose] public section

namespace EvenAssembly

open ColSplit ColUpper Polynomial EvenCount

set_option synthInstance.maxHeartbeats 200000

/-- **Hypothesis `H(m, k)`** of the Setting of `q_quartic_assembly.md`: for every prime `p`
dividing `m`, `rank_{F_p}(A) = Q^e_k(m)`, where `A = intMatU m k`. (The instance `Fact p.Prime`
making `ZMod p` a field is supplied from the primality hypothesis.) -/
def HypH (m k : ℕ) : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → p ∣ m →
    haveI := Fact.mk hp
    EveryField.rankOver (ZMod p) (intMatU m k) = QkEven k m

/-- **Proof of (i)**, case *characteristic `p > 0`, `p ∤ m`*, in `q_quartic_assembly.md`: if `K`
is algebraically closed, `m` is even and `m ≠ 0` in `K`, then `dim_K I_K = |Γ| = Q^e_k(m)` by
(ii) of `q_col_upper.md` and (v) of `q_even_count.md`. -/
theorem finrank_IK_of_isAlgClosed_even (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ}
    (heven : Even m) (h2 : 2 ≤ m) (hne : (m : K) ≠ 0) (k : ℕ) :
    Module.finrank K ((IK K m k).restrictScalars K) = QkEven k m := by
  obtain ⟨hprod, -⟩ := ColAssembly.prod_nthRootsFinset_of_isAlgClosed K (by omega) hne
  rw [finrank_IK_eq_card_Gamma hprod k, card_Gamma_even hprod hne heven k]

/-- **Proof of (i)**, case *characteristic `p > 0`, `p ∤ m`*, in `q_quartic_assembly.md`: for a
field `F` of characteristic `p` with `p ∤ m` (`m ≥ 2` even),
`rank_F(A) = rank_{F_p}(A) = rank_K(A) = Q^e_k(m)`, with `K` an algebraic closure of `F_p`. -/
theorem rankOver_of_charP_not_dvd (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {m : ℕ} (heven : Even m) (h2 : 2 ≤ m) (hdvd : ¬ p ∣ m) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = QkEven k m := by
  rw [ColAssembly.rankOver_eq_rankOver_zmod F p,
    ← ColAssembly.rankOver_eq_rankOver_zmod (AlgebraicClosure (ZMod p)) p,
    ← finrank_IK_eq_rankOver (by omega)]
  refine finrank_IK_of_isAlgClosed_even _ heven h2 ?_ k
  rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
  exact hdvd

/-- **Theorem (i)** of `q_quartic_assembly.md`, matrix form (away from the primes of `m`): for
even `m ≥ 2` and a field `F` with `m ≠ 0` in `F`, `rank_F(A) = Q^e_k(m)`. -/
theorem rankOver_intMatU_of_ne_zero (F : Type*) [Field F] {m : ℕ} (heven : Even m)
    (h2 : 2 ≤ m) (hne : (m : F) ≠ 0) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = QkEven k m := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · haveI := Fact.mk hp
    refine rankOver_of_charP_not_dvd F p heven h2 ?_ k
    rwa [Ne, CharP.cast_eq_zero_iff F p] at hne
  · haveI : CharZero F := CharP.charP_to_charZero F
    rw [EveryField.rankOver_eq_rankOver_rat, rankOver_rat_intMatU_even heven h2]

/-- **Theorem (i)** of `q_quartic_assembly.md` (away from the primes of `m`): let `m ≥ 2` be even
and `F` a field with `m ≠ 0` in `F`. Then `rank_F(A) = Q^e_k(m)` and `dim_F I_F = Q^e_k(m)`. -/
theorem theorem_i (F : Type*) [Field F] {m : ℕ} (heven : Even m) (h2 : 2 ≤ m)
    (hne : (m : F) ≠ 0) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = QkEven k m ∧
      Module.finrank F ((IK F m k).restrictScalars F) = QkEven k m := by
  have h := rankOver_intMatU_of_ne_zero F heven h2 hne k
  exact ⟨h, by rw [finrank_IK_eq_rankOver (by omega), h]⟩

/-- **Theorem (ii)** of `q_quartic_assembly.md`, matrix form (every field, under `H`): for even
`m ≥ 2` with `H(m, k)`, `rank_F(A) = Q^e_k(m)` for every field `F`. -/
theorem rankOver_intMatU_of_H (F : Type*) [Field F] {m k : ℕ} (heven : Even m) (h2 : 2 ≤ m)
    (hH : HypH m k) :
    EveryField.rankOver F (intMatU m k) = QkEven k m := by
  by_cases hne : (m : F) ≠ 0
  · exact rankOver_intMatU_of_ne_zero F heven h2 hne k
  · push_neg at hne
    obtain ⟨p, hchar⟩ := CharP.exists F
    rcases CharP.char_is_prime_or_zero F p with hp | rfl
    · haveI := Fact.mk hp
      rw [ColAssembly.rankOver_eq_rankOver_zmod F p]
      exact hH p hp ((CharP.cast_eq_zero_iff F p m).1 hne)
    · haveI : CharZero F := CharP.charP_to_charZero F
      exact absurd hne (Nat.cast_ne_zero.2 (by omega))

/-- **Theorem (ii)** of `q_quartic_assembly.md` (every field, under `H`): let `m ≥ 2` be even and
assume `H(m, k)`. Then for every field `F`, `rank_F(A) = Q^e_k(m)` and `dim_F I_F = Q^e_k(m)`. -/
theorem theorem_ii (F : Type*) [Field F] {m k : ℕ} (heven : Even m) (h2 : 2 ≤ m)
    (hH : HypH m k) :
    EveryField.rankOver F (intMatU m k) = QkEven k m ∧
      Module.finrank F ((IK F m k).restrictScalars F) = QkEven k m := by
  have h := rankOver_intMatU_of_H F heven h2 hH
  exact ⟨h, by rw [finrank_IK_eq_rankOver (by omega), h]⟩

end EvenAssembly

end
