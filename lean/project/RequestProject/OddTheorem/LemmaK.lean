module

public import RequestProject.OddLayers.Main
public import RequestProject.Lifts.Main

/-!
# Part K of `q_oddbox_theorem.md`: the case lemma

This file formalizes **Lemma K** (the case lemma, the analogue of `Lifts.cases_of_FLam`) of
`q_oddbox_theorem.md`.

Throughout, `h` is a natural number, shapes are `OddShapes.Shape = Partition × Bool`
(`true` = marked), and `Λ` is an interlaced pair of level `n + 1`.
-/

@[expose] public section

namespace OddTheorem

open ChainLemma ChainLemma.Partition OddShapes Tight

/-- Auxiliary for **Lemma K** of `q_oddbox_theorem.md` (first sentence of its proof, by
`OddShapes.optS_filter_eq_Icc`): for `Λ` interlaced of level `n + 1`, `(μ, δ) ∈ Sh h n` and
`1 ≤ p ≤ 2h + 1`, `optS h (μ, δ) p ∈ Λ ↔ p ≤ F_Λ(μ, δ)`. -/
theorem optS_mem_iff {h n : ℕ} {Lam : Set Shape} (hΛ : IsInterlaced h (n + 1) Lam)
    {mu : Partition} {d : Bool} (hs : (mu, d) ∈ Sh h n) {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 2 * h + 1) : optS h (mu, d) p ∈ Lam ↔ p ≤ FS h Lam (mu, d) := by
  classical
  have e := optS_filter_eq_Icc (m := n + 1) (by omega) hΛ (by simpa using hs)
  have := congrArg (fun A => p ∈ A) e
  simp only [Finset.mem_filter, Finset.mem_Icc, eq_iff_iff] at this
  constructor
  · intro hm; exact (this.1 ⟨⟨hp1, hp⟩, hm⟩).2
  · intro hle; exact (this.2 ⟨hp1, hle⟩).2

/-- Auxiliary for **Lemma K** and **(P0)**, **(P1)** of `q_oddbox_theorem.md`
("`FS ≤ 2h + 1` follows from `OddShapes.FS_eq_card`"): for `ℓ(μ) ≤ h`, `F_Λ(μ, δ) ≤ 2h + 1`. -/
theorem FS_le {h : ℕ} (Lam : Set Shape) {mu : Partition} (d : Bool) (hl : mu.len ≤ h) :
    FS h Lam (mu, d) ≤ 2 * h + 1 := by
  classical
  rw [FS_eq_card h Lam mu d hl]
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- **Lemma K** (the case lemma) of `q_oddbox_theorem.md`. Let `Λ` be interlaced of level `n + 1`,
`(μ, δ) ∈ Sh h n` and `Φ := F_Λ(μ, δ) ≥ 1`; write `low := if δ then 2 else 1`. Then at least one
of:
* **(A)** there are `λ` with `(λ, δ) ∈ Λ` and `c* ≥ low` with `λ'_c = μ'_c + [c = c*]` for every
  `c ≥ 1`, and `μ'_{c*} + Φ = 2h + 1`;
* **(M)** `δ = true`, `(μ ⊔ 1, true) ∈ Λ`, `(μ, false) ∈ Λ`, `ℓ(μ) < h` and `Φ = 2h + 1 − ℓ(μ)`;
* **(Z)** `(μ, !δ) ∈ Λ` and `Φ = ℓ(μ) + 1`;
* **(R)** there are `λ` with `(λ, δ) ∈ Λ` and `c_0 ≥ low` with `λ'_c + [c = c_0] = μ'_c` for every
  `c ≥ 1`, and `μ'_{c_0} = Φ`;
* **(R1)** `δ = true`, `1 ≤ ℓ(μ)`, `μ_ℓ = 1`, `(μ − e_ℓ, true) ∈ Λ` and `Φ = ℓ(μ)`.

The hypothesis `1 ≤ h` of the file is not needed and is omitted (the statement is more general). -/
theorem lemmaK {h n : ℕ} {Lam : Set Shape} (hΛ : IsInterlaced h (n + 1) Lam)
    {mu : Partition} {d : Bool} (hs : (mu, d) ∈ Sh h n) (hΦ : 1 ≤ FS h Lam (mu, d)) :
    (∃ lam, (lam, d) ∈ Lam ∧ ∃ cs, (if d then 2 else 1) ≤ cs ∧
        (∀ c, 1 ≤ c → colLen lam c = colLen mu c + if c = cs then 1 else 0) ∧
        colLen mu cs + FS h Lam (mu, d) = 2 * h + 1) ∨
    (d = true ∧ (mu.addOne, true) ∈ Lam ∧ (mu, false) ∈ Lam ∧ mu.len < h ∧
        FS h Lam (mu, d) = 2 * h + 1 - mu.len) ∨
    ((mu, !d) ∈ Lam ∧ FS h Lam (mu, d) = mu.len + 1) ∨
    (∃ lam, (lam, d) ∈ Lam ∧ ∃ c0, (if d then 2 else 1) ≤ c0 ∧
        (∀ c, 1 ≤ c → colLen lam c + (if c = c0 then 1 else 0) = colLen mu c) ∧
        colLen mu c0 = FS h Lam (mu, d)) ∨
    (d = true ∧ 1 ≤ mu.len ∧ mu.row mu.len = 1 ∧ (mu.subE mu.len, true) ∈ Lam ∧
        FS h Lam (mu, d) = mu.len) := by
  set Φ := FS h Lam (mu, d) with hΦdef
  have hl : mu.len ≤ h := hs.1
  have hΦr : Φ ≤ 2 * h + 1 := FS_le Lam d hl
  have hin : ∀ p, 1 ≤ p → p ≤ 2 * h + 1 → (optS h (mu, d) p ∈ Lam ↔ p ≤ Φ) :=
    fun p hp1 hp => optS_mem_iff hΛ hs hp1 hp
  have hSh : ∀ p, 1 ≤ p → p ≤ 2 * h + 1 → optS h (mu, d) p ∈ Sh h (n + 1) := fun p hp1 hp =>
    optS_mem_Sh (m := n + 1) (by omega) (by simpa using hs) hp1 hp
  have hoptΦ := (hin Φ hΦ hΦr).2 le_rfl
  rcases Nat.lt_or_ge mu.len Φ with hgt | hrem
  · rcases Nat.lt_or_ge (mu.len + 1) Φ with hgt2 | hz
    · by_cases hmid : Φ ≤ 2 * h + 1 - mu.len
      · -- the middle option
        rw [OddLayers.optS_mid h mu d hgt2 hmid] at hoptΦ
        have hΦeq : Φ = 2 * h + 1 - mu.len := by
          by_contra hne
          have h1 := (hin (Φ + 1) (by omega) (by omega)).1
            (by rw [OddLayers.optS_mid h mu d (by omega) (by omega)]; exact hoptΦ)
          omega
        cases d with
        | false =>
          left
          refine ⟨_, hoptΦ, 1, by simp, fun c hc => Lifts.colLen_addOne mu hc, ?_⟩
          rw [Lifts.colLen_one]; omega
        | true =>
          right; left
          have hz := (hin (mu.len + 1) (by omega) (by omega)).2 (by omega)
          rw [optS_len_succ] at hz
          exact ⟨rfl, hoptΦ, hz, by omega, hΦeq⟩
      · -- an addition
        left
        set j0 := 2 * h + 2 - Φ with hj0
        have hj01 : 1 ≤ j0 := by omega
        have hj0l : j0 ≤ mu.len := by omega
        rw [OddLayers.optS_add h mu d hgt2 (by omega)] at hoptΦ
        refine ⟨_, hoptΦ, mu.row j0 + 1, ?_, fun c _ => Lifts.colLen_addE mu hj01 hj0l c, ?_⟩
        · have := mu.row_pos j0 hj01 hj0l
          split_ifs <;> omega
        rw [Lifts.colLen_row_succ mu hj01 hj0l (fun h2 => ?_)]
        · omega
        have hle := mu.row_anti (j0 - 1) j0 (by omega) (by omega) hj0l
        by_contra hne
        have heq : mu.row (j0 - 1) = mu.row j0 := by omega
        have hopt' : optS h (mu, d) (Φ + 1) = (mu.addE (j0 - 1), d) := by
          rw [OddLayers.optS_add h mu d (by omega) (by omega)]
          congr 2
        have hmem : optS h (mu, d) (Φ + 1) ∈ Lam := by
          have hS := hSh (Φ + 1) (by omega) (by omega)
          rw [hopt'] at hS ⊢
          exact hΛ.down hS (Lifts.addE_le_of_row_eq mu (by omega) (by omega) hj01 hj0l heq)
            hoptΦ
        have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
        omega
    · -- the zero option
      have hΦeq : Φ = mu.len + 1 := by omega
      right; right; left
      rw [hΦeq, optS_len_succ] at hoptΦ
      exact ⟨hoptΦ, hΦeq⟩
  · -- a removal
    rw [OddLayers.optS_rem h mu d hrem] at hoptΦ
    have hlast : Φ < mu.len → mu.row (Φ + 1) < mu.row Φ := by
      intro hlt
      have hle := mu.row_anti Φ (Φ + 1) hΦ (by omega) hlt
      by_contra hne
      have heq : mu.row (Φ + 1) = mu.row Φ := by omega
      have hmem : optS h (mu, d) (Φ + 1) ∈ Lam := by
        have hS := hSh (Φ + 1) (by omega) (by omega)
        rw [OddLayers.optS_rem h mu d hlt] at hS ⊢
        exact hΛ.down hS (Lifts.subE_le_of_row_eq mu (by omega) hlt hΦ hrem heq) hoptΦ
      have := (hin (Φ + 1) (by omega) (by omega)).1 hmem
      omega
    have hcol := Lifts.colLen_row mu hΦ hrem hlast
    have hpos := mu.row_pos Φ hΦ hrem
    by_cases hR : d = false ∨ 2 ≤ mu.row Φ
    · right; right; right; left
      refine ⟨_, hoptΦ, mu.row Φ, ?_, fun c hc => Lifts.colLen_subE mu hΦ hrem hc, hcol⟩
      rcases hR with rfl | h2
      · simpa using hpos
      · split_ifs <;> omega
    · right; right; right; right
      push_neg at hR
      obtain ⟨hd, h1⟩ := hR
      have hd' : d = true := by simpa using hd
      have hr1 : mu.row Φ = 1 := by omega
      have hΦl : Φ = mu.len := by
        by_contra hne
        have := hlast (by omega)
        have := mu.row_pos (Φ + 1) (by omega) (by omega)
        omega
      refine ⟨hd', by omega, by rw [← hΦl]; exact hr1, ?_, hΦl⟩
      rw [← hΦl, ← hd']; exact hoptΦ

end OddTheorem
