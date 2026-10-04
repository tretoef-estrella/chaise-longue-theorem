module

public import RequestProject.BipInd.Main
public import RequestProject.BipAny.Lifts
public import RequestProject.BipAny.Swap
public import RequestProject.BipAny.Binomial

/-!
# Theorem 7.6′, Theorem C′ and Corollary P of `q_any_bip.md`

Formalization of **Theorem 7.6′** (bipartite down-set theorem, every `q ≥ 2`), **Theorem C′** (the
bipartite count, every `q ≥ 2`) and **Corollary P** (prime powers, the prime `2` included) of
`q_any_bip.md`, with the proofs of the file.  **Lemma P** is in
`RequestProject/BipAny/Binomial.lean`.  All objects (`Bip.R`, `Bip.BPar`, `Bip.IsDownSetB`,
`Bip.ZLam`, `Bip.VLamB`, `Bip.Ibal`, `Bip.Iph`, `Bip.Nbal`, `Bip.Nph`, `Bip.Wslice`,
`Bip.LamLayer`, `Bip.swapSet`, `Bip.swapR`) are the existing ones, unchanged.

The statements are those of `Bip.thm76` and `Bip.theoremC` with `2 ≤ q` instead of `3 ≤ q` and
without the hypothesis that `q` is odd.
-/

@[expose] public section

open MvPolynomial

namespace BipAny

open Bip ChainLemma

set_option synthInstance.maxHeartbeats 200000

variable (F : Type*) [Field F] {q : ℕ}

/-- `q_any_bip.md`, **Proof of Theorem 7.6′**, step `α ≥ 1`: by items 1, 3, 4, 5 and the induction
hypothesis for the layers `Λ_i` (down-sets of `BPar_q(α − 1, β)`),
`dim V_Λ = Σ_i dim W_{q−1−i}(V_Λ) ≥ Σ_i dim V_{Λ_i} ≥ Σ_i |Z_{Λ_i}| = Σ_i |Z_{>i}| = |Z_Λ|`.
Same statement as `Bip.card_ZLam_le_of_peel`, with `q ≥ 2` and without parity. -/
theorem card_ZLam_le_of_peel (hq : 2 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q) {α β : ℕ} (hα : 1 ≤ α)
    {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (IH : ∀ Λ' : Set (Partition × Partition), IsDownSetB q (α - 1) β Λ' →
      (ZLam Ω (α - 1) β Λ').card ≤ Module.finrank F ((VLamB F q (α - 1) β Λ').restrictScalars F)) :
    (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  rw [BipAny.card_eq_sum_Zgt_bip hq hα hΩ, BipAny.finrank_eq_sum_Wslice hq hα,
    ← Finset.sum_range_reflect (fun j => Module.finrank F (Wslice F q hα (VLamB F q α β Λ) j)) q]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ q - 1 := by
    rw [Finset.mem_range] at hi
    omega
  rw [BipAny.lemma73_ii_Zgt hq hΩ hα hΛ i,
    Finset.card_image_of_injective _ (tailToTuple_bijective hα).1]
  calc (ZLam Ω (α - 1) β (LamLayer q α β Λ i)).card
      ≤ Module.finrank F ((VLamB F q (α - 1) β (LamLayer q α β Λ i)).restrictScalars F) :=
        IH _ ((BipAny.prop74_ii hq hα hΛ).2 i)
    _ ≤ Module.finrank F (Wslice F q hα (VLamB F q α β Λ) (q - 1 - i)) :=
        Submodule.finrank_mono fun g hg => BipAny.prop75 hq hbin hα Λ hΛ i hi' hg

/-- **Theorem 7.6′** of `q_any_bip.md` (bipartite down-set theorem, every `q ≥ 2`): let `F` be a
field and `q ≥ 2` (odd or even) with `C(q−1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`, and `Ω` a finite
set with `|Ω| = q`.  For all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`,
`dim V_Λ ≥ |Z_Λ|`.  This is `Bip.thm76` with `2 ≤ q` instead of `3 ≤ q` and no parity hypothesis.
The proof is the induction on `α + β` of the file: base `Bip.card_ZLam_le_base`, step `α ≥ 1`
`card_ZLam_le_of_peel`, step `α = 0` by the swap (Lemma S (ii) `Bip.lemmaS_ii` and the parity-free
Lemma S (iii) `BipAny.lemmaS_iii`, item 6). -/
theorem thm76_any (hq : 2 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q) (α β : ℕ)
    (Λ : Set (Partition × Partition)) (hΛ : IsDownSetB q α β Λ) :
    (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) := by
  suffices H : ∀ n α β, α + β = n → ∀ Λ : Set (Partition × Partition), IsDownSetB q α β Λ →
      (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) from
    H _ α β rfl Λ hΛ
  intro n
  induction n with
  | zero =>
    intro α β h Λ _
    obtain ⟨rfl, rfl⟩ : α = 0 ∧ β = 0 := by omega
    exact card_ZLam_le_base F hΩ Λ
  | succ n ih =>
    intro α β h Λ hΛ
    rcases Nat.eq_zero_or_pos α with rfl | hα
    · -- case `α = 0`: the swap (Lemma S)
      have hβ : 1 ≤ β := by omega
      have hsw := BipAny.card_ZLam_le_of_peel F hq hbin hΩ hβ (isDownSetB_swapSet hΛ)
        (fun Λ' hΛ' => ih _ _ (by omega) Λ' hΛ')
      rw [(lemmaS_ii Ω 0 β Λ).2.2, (BipAny.lemmaS_iii F q 0 β Λ).2] at hsw
      exact hsw
    · -- case `α ≥ 1`: peeling `x_1`
      exact BipAny.card_ZLam_le_of_peel F hq hbin hΩ hα hΛ
        (fun Λ' hΛ' => ih _ _ (by omega) Λ' hΛ')

/-- **Theorem C′** of `q_any_bip.md` (the bipartite count, every `q ≥ 2`): for a field `F` and
`q ≥ 2` (odd or even) with `C(q−1, t) ≠ 0` in `F` for `0 ≤ t ≤ q − 1`, and every `a ≥ 0`:
`dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`.  This is
`Bip.theoremC` with `2 ≤ q` instead of `3 ≤ q` and no parity hypothesis; proof by Lemma 7.2 and
Theorem 7.6′ (`thm76_any`). -/
theorem theoremC_any (hq : 2 ≤ q)
    (hbin : ∀ t, t ≤ q - 1 → (((q - 1).choose t : ℕ) : F) ≠ 0) (a : ℕ) :
    Nbal a q ≤ Module.finrank F ((Ibal F q a).restrictScalars F) ∧
      Nph a q ≤ Module.finrank F ((Iph F q a).restrictScalars F) ∧
      Nph a q = Nbal (a + 1) q := by
  have hΩ : Fintype.card (Fin q) = q := Fintype.card_fin q
  obtain ⟨hD1, hV1, hZ1⟩ := lemma72_i F hΩ a
  obtain ⟨hD2, hV2, hZ2⟩ := lemma72_ii F (by omega) hΩ a
  refine ⟨?_, ?_, lemma72_iii a q⟩
  · rw [← hV1, ← hZ1]
    exact thm76_any F hq hbin hΩ a a _ hD1
  · rw [← hV2, ← hZ2]
    exact thm76_any F hq hbin hΩ (a + 1) a _ hD2

/-- `q = p^v ≥ 2` for a prime `p` and `v ≥ 1` (used in the **Proof of Corollary P** of
`q_any_bip.md`). -/
theorem two_le_prime_pow {p v : ℕ} (hp : p.Prime) (hv : 1 ≤ v) : 2 ≤ p ^ v :=
  hp.two_le.trans (Nat.le_self_pow (by omega) p)

/-- **Corollary P** of `q_any_bip.md`, first statement (prime powers, the prime `2` included): let
`p` be a prime, `v ≥ 1`, `q = p^v`, `F` a field of characteristic `p`, and `Ω` a finite set with
`|Ω| = q`.  Then for all `α, β ≥ 0` and every down-set `Λ` of `BPar_q(α, β)`,
`dim V_Λ ≥ |Z_Λ|`.  Proof: Lemma P (`choose_pred_prime_pow_ne_zero`) and `q ≥ 2`, then
Theorem 7.6′ (`thm76_any`). -/
theorem thm76_prime_pow {p v : ℕ} (hp : p.Prime) (hv : 1 ≤ v) (hqpv : q = p ^ v) [CharP F p]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = q) (α β : ℕ)
    (Λ : Set (Partition × Partition)) (hΛ : IsDownSetB q α β Λ) :
    (ZLam Ω α β Λ).card ≤ Module.finrank F ((VLamB F q α β Λ).restrictScalars F) :=
  thm76_any F (hqpv ▸ two_le_prime_pow hp hv) (choose_pred_prime_pow_ne_zero F hp hv hqpv) hΩ
    α β Λ hΛ

/-- **Corollary P** of `q_any_bip.md`, second statement (prime powers, the prime `2` included): let
`p` be a prime, `v ≥ 1`, `q = p^v` and `F` a field of characteristic `p`.  Then for every `a ≥ 0`,
`dim I^{bal}_a ≥ N_{bal}(a, q)` and `dim I^{ph}_a ≥ N_{ph}(a, q) = N_{bal}(a + 1, q)`.  In
particular this holds for `q = 2^v` and `F` of characteristic `2`.  Proof: Lemma P and `q ≥ 2`,
then Theorem C′ (`theoremC_any`). -/
theorem theoremC_prime_pow {p v : ℕ} (hp : p.Prime) (hv : 1 ≤ v) (hqpv : q = p ^ v) [CharP F p]
    (a : ℕ) :
    Nbal a q ≤ Module.finrank F ((Ibal F q a).restrictScalars F) ∧
      Nph a q ≤ Module.finrank F ((Iph F q a).restrictScalars F) ∧
      Nph a q = Nbal (a + 1) q :=
  theoremC_any F (hqpv ▸ two_le_prime_pow hp hv) (choose_pred_prime_pow_ne_zero F hp hv hqpv) a

end BipAny

end
