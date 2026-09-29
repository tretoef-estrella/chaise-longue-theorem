module

public import Mathlib

/-!
# Perfect matchings of a finite set (`q_col_compatible.md`, Proof of Lemma 6.3 (iv))

A perfect matching of a finite set `T` is encoded, as in `q_col_survivors.md` and
`q3_ballot_lower_bound.md` (`BallotBound.Matching`), by the fixed-point-free involution sending an
element to its partner.  The **Proof** of Lemma 6.3 (iv) in `q_col_compatible.md` uses that the
number of fixed-point-free involutions of a set of even size `2s` is `(2s − 1)!!` (and there are
none on a set of odd size).
-/

@[expose] public section

namespace ColComp

/-- **Lemma 6.3 (iii)** of `q_col_compatible.md`: a perfect matching of a type `T`, i.e. a
fixed-point-free involution of `T` (the same encoding as `BallotBound.Matching k`, which is
`PerfMatch (Fin (2 * k + 2))` by definition). -/
def PerfMatch (T : Type*) : Type _ := {P : T → T // ∀ x, P x ≠ x ∧ P (P x) = x}

namespace PerfMatch

variable {T : Type*}

/-- Two perfect matchings are equal as soon as they agree pointwise (used in the **Proof** of
Lemma 6.3 (iii) of `q_col_compatible.md`). -/
theorem ext {P Q : PerfMatch T} (h : ∀ x, P.1 x = Q.1 x) : P = Q :=
  Subtype.ext (funext h)

/-- Perfect matchings of `T` are the permutations of `T` that are fixed-point-free involutions
(used in the **Proof** of Lemma 6.3 (iv) of `q_col_compatible.md`). -/
def equivPerm : PerfMatch T ≃ {g : Equiv.Perm T // ∀ x, g x ≠ x ∧ g (g x) = x} where
  toFun P := ⟨Function.Involutive.toPerm P.1 (fun x => (P.2 x).2), P.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv P := rfl
  right_inv g := by
    apply Subtype.ext
    ext x
    rfl

variable [Fintype T] [DecidableEq T]

/-- A permutation is a fixed-point-free involution iff `|T|` is even and its cycle type consists
of `|T|/2` cycles of length `2` (used in the **Proof** of Lemma 6.3 (iv) of
`q_col_compatible.md`). -/
theorem prop_iff_cycleType (g : Equiv.Perm T) :
    (∀ x, g x ≠ x ∧ g (g x) = x) ↔
      Even (Fintype.card T) ∧ g.cycleType = Multiset.replicate (Fintype.card T / 2) 2 := by
  constructor
  · intro h
    have hsupp : g.support = Finset.univ := by
      ext x; simp [(h x).1]
    have hord : orderOf g ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      ext x; simp [sq, (h x).2]
    have h2 : ∀ b ∈ g.cycleType, b = 2 := fun b hb =>
      le_antisymm (Nat.le_of_dvd two_pos ((Equiv.Perm.dvd_of_mem_cycleType hb).trans hord))
        (Equiv.Perm.two_le_of_mem_cycleType hb)
    have hrep : g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 2 :=
      Multiset.eq_replicate.2 ⟨rfl, h2⟩
    have hsum := Equiv.Perm.sum_cycleType g
    rw [hsupp, Finset.card_univ, hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    refine ⟨⟨Multiset.card g.cycleType, by omega⟩, ?_⟩
    rw [hrep, ← hsum]
    congr 1
    omega
  · rintro ⟨⟨s, hs⟩, hct⟩ x
    have hsum := Equiv.Perm.sum_cycleType g
    rw [hct, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsupp : g.support = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [← hsum]; omega)
    have hord : orderOf g ∣ 2 := by
      rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
      intro b hb
      rw [hct] at hb
      rw [Multiset.eq_of_mem_replicate hb]
    have hsq : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
    refine ⟨?_, ?_⟩
    · have : x ∈ g.support := hsupp ▸ Finset.mem_univ x
      exact Equiv.Perm.mem_support.1 this
    · have := congrArg (fun f : Equiv.Perm T => f x) hsq
      simpa [sq] using this

/-- **Proof** of Lemma 6.3 (iv) in `q_col_compatible.md`: the number of fixed-point-free
involutions (perfect matchings) of a finite set `T` is `(|T| − 1)!!` if `|T|` is even (with
`(−1)!! = 1`), and `0` if `|T|` is odd. -/
theorem card_perfMatch :
    Nat.card (PerfMatch T) =
      if Even (Fintype.card T) then (Fintype.card T - 1).doubleFactorial else 0 := by
  classical
  rw [Nat.card_congr equivPerm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [prop_iff_cycleType]
  split_ifs with he
  · simp only [he, true_and]
    rw [Equiv.Perm.card_of_cycleType]
    obtain ⟨s, hs⟩ := he
    have hn : Fintype.card T = 2 * s := by omega
    rw [hn, show 2 * s / 2 = s by omega]
    simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate, Multiset.mem_replicate,
      ne_eq, and_imp]
    rw [if_pos ⟨by omega, fun a _ h => by omega⟩]
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp
    · rw [Multiset.toFinset_replicate, if_neg (by omega), Finset.prod_singleton,
        Multiset.count_replicate_self, show 2 * s - s * 2 = 0 by omega, Nat.factorial_zero,
        one_mul]
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring, Nat.doubleFactorial_two_mul,
        show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
      rw [mul_comm, Nat.mul_div_cancel]
      positivity
  · simp [he]

/-- **Proof** of Lemma 6.3 (iv) in `q_col_compatible.md`: a finite set has a perfect matching
(fixed-point-free involution) iff its cardinality is even. -/
theorem nonempty_perfMatch_iff : Nonempty (PerfMatch T) ↔ Even (Fintype.card T) := by
  classical
  haveI : Finite (PerfMatch T) := Finite.of_injective (fun P : PerfMatch T => P.1)
    (fun _ _ h => Subtype.ext h)
  rw [← Nat.card_pos_iff.trans (and_iff_left (by infer_instance)), card_perfMatch]
  split_ifs with he
  · simp [he, Nat.doubleFactorial_pos]
  · simp [he]

end PerfMatch

end ColComp

end
