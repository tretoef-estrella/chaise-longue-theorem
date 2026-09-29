module

public import RequestProject.Monotone.Lemmas

/-!
# Options are monotone in the partition (`q_P2_monotone_options.md`)

This file proves the **Proposition** and the **Corollary** of `q_P2_monotone_options.md`,
reusing the definitions of `RequestProject/Chain/Defs.lean` (the **Setting** of
`q_chain_lemma.md`). `μ̃` of the file is written `ν`, and `L = 2h` is written `2 * h`.
-/

@[expose] public section

namespace ChainLemma

open Partition

/-- **Proposition** of `q_P2_monotone_options.md`: let `h ≥ 1` and `L := 2h`. If `μ, μ̃` are
partitions with `ℓ(μ) ≤ h`, `ℓ(μ̃) ≤ h`, `|μ| ≡ |μ̃| (mod 2)` and `μ ≼ μ̃`, then
`opt_p(μ) ≼ opt_p(μ̃)` for every `p = 1, …, L`. (Here `μ̃` is `ν`.)

The proof is the case analysis (a)–(e2) of the file. The hypothesis `h ≥ 1` is kept as in the
file, but the proof does not use it (for `h = 0` there is no `p` with `1 ≤ p ≤ 0`). -/
theorem opt_weakDom_opt (h : ℕ) (hh : 1 ≤ h) (μ ν : Partition) (hμ : μ.len ≤ h)
    (hν : ν.len ≤ h) (hpar : μ.size % 2 = ν.size % 2) (hle : μ ≼ ν) (p : ℕ) (hp : 1 ≤ p)
    (hpL : p ≤ 2 * h) : μ.opt (2 * h) p ≼ ν.opt (2 * h) p := by
  unfold opt
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact case_a hle hp h1 h2
  · exact case_e1 hle hp h1
  · omega
  · exact case_d1 hle hpar (by omega) h5
  · exact case_c hle
  · exact case_d2 hle (by omega) (by omega)
  · omega
  · exact case_e2 hle (by omega) (by omega)
  · exact case_b hle (by omega) (by omega) (by omega)

open Classical in
/-- **Corollary** of `q_P2_monotone_options.md`, first statement: under the hypotheses of the
Proposition (`h ≥ 1`, `L = 2h`, `ℓ(μ), ℓ(μ̃) ≤ h`, `|μ| ≡ |μ̃| (mod 2)`, `μ ≼ μ̃`), for every
down-set `Λ` of partitions, `#{p : opt_p(μ̃) ∈ Λ} ≤ #{p : opt_p(μ) ∈ Λ}`, where `p` ranges over
`1, …, L`. (Here `μ̃` is `ν`.) -/
theorem card_opt_mem_le (h : ℕ) (hh : 1 ≤ h) (μ ν : Partition) (hμ : μ.len ≤ h)
    (hν : ν.len ≤ h) (hpar : μ.size % 2 = ν.size % 2) (hle : μ ≼ ν) (Λ : Set Partition)
    (hΛ : IsDownSet Λ) :
    ((Finset.Icc 1 (2 * h)).filter (fun p => ν.opt (2 * h) p ∈ Λ)).card ≤
      ((Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ)).card := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨hp.1, hΛ _ _ (opt_weakDom_opt h hh μ ν hμ hν hpar hle p hp.1.1 hp.1.2) hp.2⟩

open Classical in
/-- **Corollary** of `q_P2_monotone_options.md`, second statement ("Consequently, …"): for every
down-set `Λ`, every `i ≥ 0` and every fixed `N`, the set
`D := {μ : ℓ(μ) ≤ h, |μ| ≡ N (mod 2), #{p : opt_p(μ) ∈ Λ} > i}` is a down-set within the
partitions of length `≤ h` and size `≡ N (mod 2)`: if `λ` is such a partition, `λ ≼ μ` and
`μ ∈ D`, then `λ ∈ D`. (Here `p` ranges over `1, …, L` with `L = 2h`, `h ≥ 1`.) -/
theorem opt_count_gt_isDownSet_within (h : ℕ) (hh : 1 ≤ h) (Λ : Set Partition)
    (hΛ : IsDownSet Λ) (i N : ℕ) (lam μ : Partition) (hlam : lam.len ≤ h)
    (hlamN : lam.size % 2 = N % 2) (hle : lam ≼ μ)
    (hμ : μ ∈ {μ : Partition | μ.len ≤ h ∧ μ.size % 2 = N % 2 ∧
      i < ((Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ)).card}) :
    lam ∈ {μ : Partition | μ.len ≤ h ∧ μ.size % 2 = N % 2 ∧
      i < ((Finset.Icc 1 (2 * h)).filter (fun p => μ.opt (2 * h) p ∈ Λ)).card} := by
  obtain ⟨h1, h2, h3⟩ := hμ
  exact ⟨hlam, hlamN, lt_of_lt_of_le h3
    (card_opt_mem_le h hh lam μ hlam h1 (by omega) hle Λ hΛ)⟩

end ChainLemma
