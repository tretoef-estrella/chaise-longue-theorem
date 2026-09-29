module

public import RequestProject.ColAssembly.Prop69
public import RequestProject.ColAssembly.Extension

/-!
# The Theorem (every field) of `q_col_assembly.md`

For odd `m ≥ 1` and every field `F`, `dim_F I_F = Q_k(m)`, equivalently `rank_F(A) = Q_k(m)` for
the integer matrix `A = ColUpper.intMatU m k` of (i) of `q_col_upper.md`
(`ColAssembly.theorem_every_field`).

The proof follows the file:
* (a) field extensions do not change `rank(A)` (`RequestProject/ColAssembly/Extension.lean`);
* (b) in characteristic `0`, `rank_F(A) = rank_ℚ(A) = Q_k(m)`;
* (c) in characteristic `p > 0`, pass to `K = AlgebraicClosure (ZMod p)`; if `p ∤ m` use the
  `m`-th roots of unity in `K` and (ii), (iii) of `q_col_upper.md`; if `p ∣ m`, write
  `m = p^v·r` with `p ∤ r`, build the Setting of `q_col_splitting.md` on `K` with `μ` the `r`-th
  roots of unity, and use Proposition 6.9.
-/

@[expose] public section

namespace ColAssembly

open ColSplit ColUpper TheoremB Polynomial

set_option synthInstance.maxHeartbeats 200000

/-- **Proof of the Theorem (every field)**, part (c), in `q_col_assembly.md`: in an algebraically
closed field `K` with `n ≠ 0` in `K` (`n ≥ 1`), `X^n − 1` has `n` distinct roots: the set `μ_n` of
`n`-th roots of unity satisfies `X^n − 1 = Π_{ξ∈μ_n} (X − ξ)` and `|μ_n| = n`. -/
theorem prod_nthRootsFinset_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] {n : ℕ}
    (hn : 0 < n) (hne : (n : K) ≠ 0) :
    (X ^ n - 1 : K[X]) = ∏ ξ ∈ nthRootsFinset n (1 : K), (X - C ξ) ∧
      (nthRootsFinset n (1 : K)).card = n := by
  haveI : NeZero (n : K) := ⟨hne⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic n K) (degree_cyclotomic_pos n K hn).ne'
  have hprim : IsPrimitiveRoot z n := isRoot_cyclotomic_iff.1 hz
  exact ⟨X_pow_sub_one_eq_prod hn hprim, hprim.card_nthRootsFinset⟩

/-- **Proof of the Theorem (every field)**, part (c), first case, in `q_col_assembly.md`: if `K`
is algebraically closed, `m` is odd and `m ≠ 0` in `K` (i.e. `p ∤ m`), then
`dim_K I_K = |Γ| = Q_k(m)` by (ii) and (iii) of `q_col_upper.md`. -/
theorem finrank_IK_of_isAlgClosed_of_ne_zero (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ}
    (hodd : Odd m) (hne : (m : K) ≠ 0) (k : ℕ) :
    Module.finrank K ((IK K m k).restrictScalars K) = Qk k m := by
  obtain ⟨hprod, -⟩ := prod_nthRootsFinset_of_isAlgClosed K hodd.pos hne
  rw [finrank_IK_eq_card_Gamma hprod k, card_Gamma hprod hne hodd k]

/-- **Proof of the Theorem (every field)**, part (c), second case, in `q_col_assembly.md`: if `K`
is algebraically closed of characteristic `p`, `m` is odd and `p ∣ m`, write `m = p^v·r` with
`v ≥ 1`, `p ∤ r`; then `K` with `(p, v, r, μ)`, `μ` the `r`-th roots of unity, satisfies the
Setting of `q_col_splitting.md` with `q·r = m`, `p ≠ 2`, `r` odd, and Proposition 6.9 gives
`dim_K I_K = Q_k(m)`. -/
theorem finrank_IK_of_isAlgClosed_of_dvd (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ)
    [hp : Fact p.Prime] [CharP K p] {m : ℕ} (hodd : Odd m) (hdvd : p ∣ m) (k : ℕ) :
    Module.finrank K ((IK K m k).restrictScalars K) = Qk k m := by
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  obtain ⟨v, r, hmr, hv, hpr⟩ : ∃ v r : ℕ, p ^ v * r = m ∧ 1 ≤ v ∧ ¬ p ∣ r :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self m p, hp.out.factorization_pos_of_dvd hm0 hdvd,
      Nat.not_dvd_ordCompl hp.out hm0⟩
  subst hmr
  have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hm0 (mul_zero _))
  have hrodd : Odd r := (Nat.odd_mul.1 hodd).2
  have hrK : (r : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    exact hpr
  obtain ⟨hprod, hcard⟩ := prod_nthRootsFinset_of_isAlgClosed K hr0 hrK
  let S : ColSetting K :=
    { p := p, hp := hp.out, charP := inferInstance, v := v, one_le_v := hv, r := r,
      one_le_r := hr0, μ := nthRootsFinset r (1 : K), card_μ := hcard, X_pow_sub_one := hprod }
  exact prop69 S hp2 hrodd

/-- **Proof of the Theorem (every field)**, part (c), in `q_col_assembly.md`: for a field `F` of
characteristic `p > 0` and odd `m`, `rank_F(A) = rank_{F_p}(A) = rank_K(A) = Q_k(m)`, where `K` is
an algebraic closure of `F_p`. -/
theorem rankOver_intMatU_of_charP (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {m : ℕ} (hodd : Odd m) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = Qk k m := by
  rw [rankOver_eq_rankOver_zmod F p,
    ← rankOver_eq_rankOver_zmod (AlgebraicClosure (ZMod p)) p, ← finrank_IK_eq_rankOver hodd.pos]
  by_cases hdvd : p ∣ m
  · exact finrank_IK_of_isAlgClosed_of_dvd _ p hodd hdvd k
  · refine finrank_IK_of_isAlgClosed_of_ne_zero _ hodd ?_ k
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
    exact hdvd

/-- **Theorem (every field)** of `q_col_assembly.md`, matrix form: for odd `m ≥ 1` and every
field `F`, `rank_F(A) = Q_k(m)`, where `A = intMatU m k` is the integer matrix of (i) of
`q_col_upper.md`. -/
theorem rankOver_intMatU (F : Type*) [Field F] {m : ℕ} (hodd : Odd m) (k : ℕ) :
    EveryField.rankOver F (intMatU m k) = Qk k m := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · haveI := Fact.mk hp
    exact rankOver_intMatU_of_charP F p hodd k
  · haveI : CharZero F := CharP.charP_to_charZero F
    rw [EveryField.rankOver_eq_rankOver_rat, rankOver_rat_intMatU hodd]

/-- **Theorem (every field)** of `q_col_assembly.md`, ideal form: for odd `m ≥ 1` and every field
`F`, `dim_F I_F = Q_k(m)`. -/
theorem finrank_IK_eq (F : Type*) [Field F] {m : ℕ} (hodd : Odd m) (k : ℕ) :
    Module.finrank F ((IK F m k).restrictScalars F) = Qk k m := by
  rw [finrank_IK_eq_rankOver hodd.pos, rankOver_intMatU F hodd k]

/-- **Theorem (every field)** of `q_col_assembly.md`: let `m ≥ 1` be odd. For every field `F`,
`dim_F I_F = Q_k(m)`; equivalently, `rank_F(A) = Q_k(m)` for the integer matrix `A = intMatU m k`
of (i) of `q_col_upper.md`. -/
theorem theorem_every_field {m : ℕ} (hodd : Odd m) (k : ℕ) (F : Type*) [Field F] :
    EveryField.rankOver F (intMatU m k) = Qk k m ∧
      Module.finrank F ((IK F m k).restrictScalars F) = Qk k m :=
  ⟨rankOver_intMatU F hodd k, finrank_IK_eq F hodd k⟩

end ColAssembly

end
