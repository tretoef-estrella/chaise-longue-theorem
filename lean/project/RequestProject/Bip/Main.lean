module

public import RequestProject.Bip.Peeling
public import RequestProject.Bip.Counts
public import RequestProject.Bip.Roots

/-!
# Lemma 7.2 of `q_bip_setting.md` (the roots)

The statements of **Lemma 7.2** (0)–(iii) of `q_bip_setting.md`, assembled from
`RequestProject/Bip/Counts.lean` and `RequestProject/Bip/Roots.lean`.  **Lemma 7.1** (i)–(iv) is
in `RequestProject/Bip/Peeling.lean` (`Bip.Wslice_isIdeal`, `Bip.Wslice_mono`,
`Bip.finrank_eq_sum_Wslice`, `Bip.card_eq_sum_Zgt_bip`).

Throughout, `Ω` is a finite type with `Fintype.card Ω = q`.  The Setting's hypotheses "`q ≥ 3`
odd" are not needed for Lemma 7.2, except that part (ii) uses `1 ≤ q`.
-/

@[expose] public section

namespace Bip

open ChainLemma

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Lemma 7.2 (0)** of `q_bip_setting.md`: for every point `(ξ, η) ∈ Ω^α × Ω^β`,
`λ(ξ, η) ∈ BPar_q(α, β)`. -/
theorem lemma72_0 {q α β : ℕ} (hΩ : Fintype.card Ω = q) (ξ : Fin α → Ω) (η : Fin β → Ω) :
    shape ξ η ∈ BPar q α β :=
  shape_mem_BPar hΩ ξ η

/-- **Lemma 7.2 (i)** of `q_bip_setting.md`: `{(∅, ∅)}` is a down-set of `BPar_q(a, a)`;
`V_{{(∅,∅)}} = I^{bal}_a`; and `|Z_{{(∅,∅)}}| = N_{bal}(a, q)`. -/
theorem lemma72_i (F : Type*) [Field F] {q : ℕ} (hΩ : Fintype.card Ω = q) (a : ℕ) :
    IsDownSetB q a a {(Partition'.empty, Partition'.empty)} ∧
      VLamB F q a a {(Partition'.empty, Partition'.empty)} = Ibal F q a ∧
      (ZLam Ω a a {(Partition'.empty, Partition'.empty)}).card = Nbal a q :=
  ⟨isDownSetB_empty q a, VLamB_empty_eq_Ibal F q a, card_ZLam_empty hΩ a⟩

/-- **Lemma 7.2 (ii)** of `q_bip_setting.md`: `{((1), ∅)}` is a down-set of `BPar_q(a + 1, a)`;
`V_{{((1),∅)}} = I^{ph}_a`; and `|Z_{{((1),∅)}}| = N_{ph}(a, q)`.  Of the Setting's hypotheses on
`q` only `1 ≤ q` is used (for `((1), ∅) ∈ BPar_q(a + 1, a)`). -/
theorem lemma72_ii (F : Type*) [Field F] {q : ℕ} (hq : 1 ≤ q) (hΩ : Fintype.card Ω = q)
    (a : ℕ) :
    IsDownSetB q (a + 1) a {(Partition'.one, Partition'.empty)} ∧
      VLamB F q (a + 1) a {(Partition'.one, Partition'.empty)} = Iph F q a ∧
      (ZLam Ω (a + 1) a {(Partition'.one, Partition'.empty)}).card = Nph a q :=
  ⟨isDownSetB_one hq a, VLamB_one_eq_Iph F q a, card_ZLam_one hΩ a⟩

/-- **Lemma 7.2 (iii)** of `q_bip_setting.md`: `N_{ph}(a, q) = N_{bal}(a + 1, q)`. -/
theorem lemma72_iii (a q : ℕ) : Nph a q = Nbal (a + 1) q :=
  Nph_eq_Nbal a q

end Bip

end
