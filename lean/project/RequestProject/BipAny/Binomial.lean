module

public import Mathlib

/-!
# Lemma P of `q_any_bip.md` (the binomial coefficients at a prime power)

**Lemma P** of `q_any_bip.md`: for a prime `p` (`p = 2` allowed), `v ≥ 1`, `q = p^v` and a field
`F` of characteristic `p`, `C(q − 1, t) = (−1)^t` in `F` for `0 ≤ t ≤ q − 1`; in particular these
binomial coefficients are non-zero in `F`.  (Compare `ColPairs.choose_q_sub_one_eq`, stated for a
`ColSetting`; here no restriction on `p` is made.)  As in `ColPairs.choose_q_sub_one_eq`, the proof
uses Pascal's rule and `p ∣ C(q, s)` for `0 < s < q` (`Nat.Prime.dvd_choose_pow`), which is the
content of `(1 + u)^q = 1 + u^q` in the **Proof** of Lemma P.
-/

@[expose] public section

namespace BipAny

/-- **Lemma P** of `q_any_bip.md`, main statement: let `p` be a prime (`p = 2` is allowed),
`v ≥ 1`, `q = p^v`, and `F` a field of characteristic `p`.  Then `C(q − 1, t) = (−1)^t` in `F` for
`0 ≤ t ≤ q − 1`.  (The hypothesis `v ≥ 1` of the file is kept; the proof does not need it, since
for `v = 0` only `t = 0` occurs.) -/
theorem choose_pred_prime_pow (F : Type*) [Field F] {p v q : ℕ} (hp : p.Prime) (hv : 1 ≤ v)
    (hqpv : q = p ^ v) [CharP F p] :
    ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) = (-1) ^ t := by
  have hq1 : 1 ≤ q := hqpv ▸ Nat.one_le_pow _ _ hp.pos
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hdvd : p ∣ q.choose (t + 1) := by
      rw [hqpv]
      exact hp.dvd_choose_pow (Nat.succ_ne_zero t) (by rw [← hqpv]; omega)
    have h2 : ((q.choose (t + 1) : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F p _).2 hdvd
    have e : q = (q - 1) + 1 := by omega
    rw [e, Nat.choose_succ_succ', Nat.cast_add, h1] at h2
    rw [pow_succ]
    linear_combination h2

/-- **Lemma P** of `q_any_bip.md`, "in particular": for a prime `p`, `v ≥ 1`, `q = p^v` and a field
`F` of characteristic `p`, `C(q − 1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`. -/
theorem choose_pred_prime_pow_ne_zero (F : Type*) [Field F] {p v q : ℕ} (hp : p.Prime)
    (hv : 1 ≤ v) (hqpv : q = p ^ v) [CharP F p] :
    ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0 := by
  intro t ht
  rw [choose_pred_prime_pow F hp hv hqpv t ht]
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

end BipAny

end
