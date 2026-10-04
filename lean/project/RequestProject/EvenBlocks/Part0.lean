module

public import RequestProject.ColDecomp.Main

/-!
# Part 0 of `q_even_blocks.md`: Lemma 9.4, and settings for every prime

* **(01)** `EvenBlocks.r_ne_zero`: `(S.r : F) ≠ 0` for every `S : ColSplit.ColSetting F`.
* **(02)** is in `RequestProject/EvenBlocks/Setting.lean`.
* **(03)** `EvenBlocks.lemma94`: Lemma 9.4, a restatement of `ColSplit.ColSetting.lemma61_ii`,
  `ColSurv.lemma62_iii` and `ColComp.lemma63_v_cExt` for an arbitrary `S`.
-/

@[expose] public section

namespace EvenBlocks

open ColSplit ColSurv ColComp Polynomial

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F]

/-- **Part 0, (01)** of `q_even_blocks.md`: for every Setting `S : ColSetting F`, `(S.r : F) ≠ 0`,
i.e. `p ∤ r`. Proof: `X^r − 1 = Π_{ζ∈μ}(X − ζ)` is a product of distinct linear factors, hence
separable, and `X^r − 1` is separable iff `(r : F) ≠ 0`. -/
theorem r_ne_zero (S : ColSetting F) : (S.r : F) ≠ 0 := by
  have hsep : (X ^ S.r - 1 : F[X]).Separable := by
    rw [S.X_pow_sub_one]
    exact (Polynomial.separable_prod_X_sub_C_iff' (s := S.μ) (f := id)).2
      fun x _ y _ h => h
  exact (Polynomial.X_pow_sub_one_separable_iff).1 hsep

/-- **Part 0, (01)** of `q_even_blocks.md`, equivalent form: `p ∤ r` for every Setting. -/
theorem not_p_dvd_r (S : ColSetting F) : ¬ S.p ∣ S.r := by
  haveI := S.charP
  rw [← CharP.cast_eq_zero_iff F S.p]
  exact r_ne_zero S

/-- **Part 0, (03) Lemma 9.4** of `q_even_blocks.md` (Lemmas 6.1 (ii) and 6.2 (iii), and 6.3 (v),
for every prime): for an arbitrary Setting `S : ColSetting F` — **no parity of `p`, `q` or `r` is
assumed** (`p = 2` and even `r` are allowed) —
1. `dim_F I' = Σ_{c ∈ μ^d} dim_F π_c(I')` for every ideal `I'` of `F[G]`
   (`ColSplit.ColSetting.lemma61_ii`);
2. for `c ∈ μ^{2k+1}` and a matching `J`: if some pair `0 < a < J(a)` has `c_a c_{J(a)} ≠ 1` then
   `π_c(ψ_J) = 0`; if all such pairs have `c_a c_{J(a)} = 1`, then `c_0 c_{J(0)} = 1` and
   `π_c(ψ_J) = w · Π_{a<J(a)} (t_{J(a)} − 1) · Π_{0<a<J(a)} (t_a t_{J(a)} − 1)^{q−1}` with `w` a unit
   (`ColSurv.lemma62_iii`);
3. `J` is compatible with `cExt c` iff `c_a c_{J(a)} = 1` whenever `a ≠ 0 ≠ J(a)`
   (`ColComp.lemma63_v_cExt`).
This is bookkeeping: the existing statements carry no parity hypothesis. -/
theorem lemma94 (S : ColSetting F) :
    (∀ (d : ℕ) (I' : Ideal (GA F d S.m)),
      Module.finrank F (I'.restrictScalars F) =
        ∑ c : Fin d → S.μ, Module.finrank F ((I'.map (S.piC c)).restrictScalars F)) ∧
    (∀ (k : ℕ) (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k),
      ((∃ a, 0 < a ∧ a < J.1 a ∧ cExt c a * cExt c (J.1 a) ≠ 1) → S.piC c (psi S k J) = 0) ∧
      ((∀ a, 0 < a → a < J.1 a → cExt c a * cExt c (J.1 a) = 1) →
        cExt c 0 * cExt c (J.1 0) = 1 ∧
          ∃ w : (Rc F S.q (fun i => (c i : F)))ˣ,
            S.piC c (psi S k J) =
              w * (∏ a ∈ Finset.univ.filter (fun a => a < J.1 a), (tR c (J.1 a) - 1)) *
                ∏ a ∈ Finset.univ.filter (fun a => 0 < a ∧ a < J.1 a),
                  (tR c a * tR c (J.1 a) - 1) ^ (S.q - 1))) ∧
    (∀ (k : ℕ) (c : Fin (2 * k + 1) → S.μ) (J : BallotBound.Matching k),
      Compatible (cExt c) J ↔ ∀ a, a ≠ 0 → J.1 a ≠ 0 → cExt c a * cExt c (J.1 a) = 1) :=
  ⟨fun d I' => S.lemma61_ii d I', fun _ c J => lemma62_iii S c J,
    fun _ c J => lemma63_v_cExt c J⟩

end EvenBlocks

end
