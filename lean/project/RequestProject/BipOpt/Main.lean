module

public import RequestProject.BipOpt.Fibres

/-!
# Lemma 7.3 of `q_bip_options.md` (the bipartite options, fibres and chain)

The statements of **Lemma 7.3** (i)–(v) of `q_bip_options.md`, assembled from
`RequestProject/BipOpt/Options.lean` ((i), (iii), (iv), (v)) and
`RequestProject/BipOpt/Fibres.lean` ((ii)).  The objects of the **Setting** are in
`RequestProject/BipOpt/Defs.lean`: the options `opt_p(μ)` (`Bip.bopt`), `F_Λ(μ)` (`Bip.FLamB`),
the layers `Λ_i` (`Bip.LamLayer`), the point `(u, M')` (`Bip.consPt`) and the tuple of a tail
(`Bip.tailToTuple`).

The hypotheses of the file are kept in the statements (`q ≥ 3`, `α ≥ 1`,
`μ ∈ BPar_q(α − 1, β)`, and `Λ` a down-set of `BPar_q(α, β)`); the docstrings say which of them
the proofs do not need.
-/

@[expose] public section

namespace Bip

open ChainLemma

/-- **Lemma 7.3 (i)** of `q_bip_options.md` (options stay in `BPar`): for `α ≥ 1` and
`μ ∈ BPar_q(α − 1, β)`, `opt_p(μ) ∈ BPar_q(α, β)` for every `p ∈ {1, …, q}`.  (The hypothesis
`q ≥ 3` of the Setting is kept but not needed.) -/
theorem lemma73_i {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) : ∀ p ∈ Finset.Icc 1 q, bopt q μ p ∈ BPar q α β :=
  fun _ hp => bopt_mem_BPar hα hμ (Finset.mem_Icc.1 hp).1 (Finset.mem_Icc.1 hp).2

/-- **Lemma 7.3 (ii)** of `q_bip_options.md` (fibres), main statement: for a finite set `Ω` with
`|Ω| = q`, `α ≥ 1`, `μ ∈ BPar_q(α − 1, β)` and every tail `M' = (ξ', η) ∈ Ω^{α−1} × Ω^β` with shape
`μ`, the multiset `{λ(u, M') : u ∈ Ω}` equals the multiset `{opt_p(μ) : p = 1, …, q}`.  (The
hypotheses `q ≥ 3` and `μ ∈ BPar_q(α − 1, β)` are kept but not needed: the latter follows from
`λ(M') = μ` by Lemma 7.2 (0).) -/
theorem lemma73_ii {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 3 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) (M' : (Fin (α - 1) → Ω) × (Fin β → Ω))
    (hM' : shape M'.1 M'.2 = μ) :
    Finset.univ.val.map (fun u => shape (consPt hα u M').1 (consPt hα u M').2) =
      (Finset.Icc 1 q).val.map (bopt q μ) :=
  map_shape_consPt hα hΩ M' hM'

/-- **Lemma 7.3 (ii)** of `q_bip_options.md` (fibres), first consequence: for every down-set `Λ`
of `BPar_q(α, β)` and every tail `M'` with shape `μ`, `|F(M')| = F_Λ(μ)`.  Here `F(M')` is the
fibre `{u ∈ Ω : (u, M') ∈ Z_Λ}` of Lemma 7.1 (iv) of `q_bip_setting.md` (`Peel.fiber` on the image
of `Z_Λ` under `toTuple`, over the tuple `tailToTuple M'` of the tail).  (The hypotheses `q ≥ 3`,
`μ ∈ BPar_q(α − 1, β)` and "`Λ` is a down-set" are kept but not needed.) -/
theorem lemma73_ii_fiber {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 3 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (M' : (Fin (α - 1) → Ω) × (Fin β → Ω)) (hM' : shape M'.1 M'.2 = μ) :
    (Peel.fiber ((ZLam Ω α β Λ).map toTuple) (tailToTuple M')).card = FLamB q Λ μ :=
  card_fiber_eq_FLamB hα hΩ Λ M' hM'

/-- **Lemma 7.3 (ii)** of `q_bip_options.md` (fibres), second consequence: for every down-set `Λ`
of `BPar_q(α, β)` and every `i`, `Z_{>i} = Z_{Λ_i}` with
`Λ_i := {ν ∈ BPar_q(α − 1, β) : F_Λ(ν) > i}` (`LamLayer q α β Λ i`).  Here `Z_{>i}` is the set of
Lemma 7.1 (iv) of `q_bip_setting.md` (`Peel.Zgt`) for `Z = Z_Λ`, and `Z_{Λ_i} ⊆ Ω^{α−1} × Ω^β` is
read through the tuples of the tails (`tailToTuple`, a bijection `Ω^{α−1} × Ω^β ≅ Ω^{α+β−1}`).
(The hypotheses `q ≥ 3` and "`Λ` is a down-set" are kept but not needed.) -/
theorem lemma73_ii_Zgt {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q α β : ℕ} (hq : 3 ≤ q)
    (hΩ : Fintype.card Ω = q) (hα : 1 ≤ α) {Λ : Set (Partition × Partition)}
    (hΛ : IsDownSetB q α β Λ) (i : ℕ) :
    Peel.Zgt ((ZLam Ω α β Λ).map toTuple) i =
      (ZLam Ω (α - 1) β (LamLayer q α β Λ i)).image tailToTuple :=
  Zgt_eq_ZLam_layer hα hΩ Λ i

/-- **Lemma 7.3 (iii)** of `q_bip_options.md` (chain): `opt_1(μ) ≼ opt_2(μ) ≼ ⋯ ≼ opt_q(μ)` in the
product order, stated both step by step (`opt_p(μ) ≼ opt_{p+1}(μ)` for `1 ≤ p < q`) and in
transitive form (`opt_p(μ) ≼ opt_{p'}(μ)` for `1 ≤ p ≤ p' ≤ q`).  As in the file, this part only
uses `ℓ_+ + ℓ_− ≤ q`. -/
theorem lemma73_iii {q : ℕ} (μ : Partition × Partition) (hl : μ.1.len + μ.2.len ≤ q) :
    (∀ p, 1 ≤ p → p < q → BWeakDom (bopt q μ p) (bopt q μ (p + 1))) ∧
      (∀ p p', 1 ≤ p → p ≤ p' → p' ≤ q → BWeakDom (bopt q μ p) (bopt q μ p')) :=
  ⟨fun _ hp hpq => bopt_le_bopt_succ μ hl hp hpq,
    fun _ _ hp hpp' hp'q => bopt_mono μ hl hp hpp' hp'q⟩

open Classical in
/-- **Lemma 7.3 (iv)** of `q_bip_options.md` (initial segment): for `α ≥ 1`,
`μ ∈ BPar_q(α − 1, β)` and every down-set `Λ` of `BPar_q(α, β)`,
`{p ∈ {1, …, q} : opt_p(μ) ∈ Λ} = {1, …, F_Λ(μ)}`.  (The hypothesis `q ≥ 3` is kept but not
needed.) -/
theorem lemma73_iv {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ) :
    (Finset.Icc 1 q).filter (fun p => bopt q μ p ∈ Λ) = Finset.Icc 1 (FLamB q Λ μ) :=
  bopt_mem_initial_segment hα hμ hΛ

/-- **Lemma 7.3 (v)** of `q_bip_options.md` (the three cases): for `α ≥ 1`,
`μ ∈ BPar_q(α − 1, β)`, a down-set `Λ` of `BPar_q(α, β)` and `Φ := F_Λ(μ) ≥ 1`, exactly one of
* **(α)** `CaseAlpha`: `Φ > q − ℓ_+`; with `j_0 := q + 1 − Φ ∈ {1, …, ℓ_+}`,
  `(μ_+ + e_{j_0}, μ_−) = opt_Φ(μ) ∈ Λ`, and `j_0 = 1` or `μ_{+, j_0 − 1} > μ_{+, j_0}`;
* **(β)** `CaseBeta`: `ℓ_− < Φ ≤ q − ℓ_+`; then `Φ = q − ℓ_+`, `ℓ_+ + ℓ_− < q` and
  `(μ_+ ⊔ 1, μ_−) = opt_Φ(μ) ∈ Λ`;
* **(γ)** `CaseGamma`: `1 ≤ Φ ≤ ℓ_−`; with `r := Φ`, `(μ_+, μ_− − e_r) = opt_r(μ) ∈ Λ`, and
  `r = ℓ_−` or `μ_{−, r+1} < μ_{−, r}`

holds.  (The hypothesis `q ≥ 3` is kept but not needed.) -/
theorem lemma73_v {q α β : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) {μ : Partition × Partition}
    (hμ : μ ∈ BPar q (α - 1) β) {Λ : Set (Partition × Partition)} (hΛ : IsDownSetB q α β Λ)
    (hΦ : 1 ≤ FLamB q Λ μ) :
    (CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        ¬ CaseGamma q Λ μ (FLamB q Λ μ)) ∨
      (¬ CaseAlpha q Λ μ (FLamB q Λ μ) ∧ ¬ CaseBeta q Λ μ (FLamB q Λ μ) ∧
        CaseGamma q Λ μ (FLamB q Λ μ)) :=
  three_cases hα hμ hΛ hΦ

end Bip

end
