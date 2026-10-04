module

public import RequestProject.OddTheorem.LemmaK
public import RequestProject.OddLifts2.Main

/-!
# Part P of `q_oddbox_theorem.md`: Proposition 8.10 (`V_{Λ_i} ⊆ W_{r−1−i}(V_Λ)`)

This file formalizes **(P0)**, **(P1)** and **(P) Proposition 8.10** of `q_oddbox_theorem.md`.

Throughout, `F` is a field, `h ≥ 1`, `r = 2h + 1`, `q = 2h + 2`, the rings are
`Peel.C F (2*h+2) m`, and the slice `r − 1 − i` of the paper is `Peel.W (m := n+1) _ V (2*h - i)`.
-/

@[expose] public section

namespace OddTheorem

open Peel hiding C
open Tight ChainLemma OddShapes OddPatterns Lifts OddLifts OddLifts2

set_option synthInstance.maxHeartbeats 200000

variable {F : Type*} [Field F] {h : ℕ}

/-- **(P0)** of `q_oddbox_theorem.md`: let `h ≥ 1`, `Λ` interlaced of level `n + 1`,
`(μ, false) ∈ Sh h n`, `i < F_Λ(μ, false)` and `T` a tight pattern of `μ` on all the indices of
`C_n`. Then `T.prod ∈ W_{2h−i}(V_Λ)`. (Proof: Lemma K, the lifts `OddLifts.T1`, `OddLifts.T5`,
`OddLifts.T2` and `Lifts.W_mono_le`.) -/
theorem P0 (hh : 1 ≤ h) {n : ℕ} {Lam : Set Shape} (hΛ : IsInterlaced h (n + 1) Lam)
    {mu : Partition} (hs : (mu, false) ∈ Sh h n) {i : ℕ} (hi : i < FS h Lam (mu, false))
    (T : TightPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F (2 * h + 2) ∈
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) := by
  have hl : mu.len ≤ h := hs.1
  have hΦr := FS_le (h := h) Lam false hl
  have hmono : ∀ d, d + i + 1 ≤ 2 * h + 1 →
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) d ≤
        W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) :=
    fun d hd => W_mono_le (q := 2 * h + 2) (by omega) _ _ (by omega) (by omega)
  rcases lemmaK hΛ hs (by omega) with
    ⟨lam, hlam, cs, hcs, hcol, hsum⟩ | ⟨hd, -⟩ | ⟨hz, hΦ⟩ | ⟨lam, hlam, c0, hc0, hcol, hr⟩ |
      ⟨hd, -⟩
  · simp only [Bool.false_eq_true, if_false] at hcs
    exact hmono _ (by omega) (T1 hlam T hcs hcol (by omega))
  · exact absurd hd (by simp)
  · exact hmono _ (by omega) (T5 hz T hl)
  · simp only [Bool.false_eq_true, if_false] at hc0
    exact hmono _ (by omega) (T2 hlam T hc0 hcol (by omega) (by omega))
  · exact absurd hd (by simp)

/-- **(P1)** of `q_oddbox_theorem.md`: let `h ≥ 1`, `Λ` interlaced of level `n + 1`,
`(μ, true) ∈ Sh h n`, `i < F_Λ(μ, true)` and `T` a marked pattern of `μ` on all the indices of
`C_n`. Then `T.prod ∈ W_{2h−i}(V_Λ)`. (Proof: Lemma K, the lifts `OddLifts.T3`, `OddLifts2.T7`,
`OddLifts2.T6`, `OddLifts.T4`, `OddLifts2.T8` and `Lifts.W_mono_le`.) -/
theorem P1 (hh : 1 ≤ h) {n : ℕ} {Lam : Set Shape} (hΛ : IsInterlaced h (n + 1) Lam)
    {mu : Partition} (hs : (mu, true) ∈ Sh h n) {i : ℕ} (hi : i < FS h Lam (mu, true))
    (T : MarkedPattern mu (Finset.univ : Finset (Fin n))) :
    T.prod F h ∈ W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) := by
  have hl : mu.len ≤ h := hs.1
  have hΦr := FS_le (h := h) Lam true hl
  have hmono : ∀ d, d + i + 1 ≤ 2 * h + 1 →
      W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) d ≤
        W (m := n + 1) (by omega) (VSAll F h (n + 1) Lam) (2 * h - i) :=
    fun d hd => W_mono_le (q := 2 * h + 2) (by omega) _ _ (by omega) (by omega)
  rcases lemmaK hΛ hs (by omega) with
    ⟨lam, hlam, cs, hcs, hcol, hsum⟩ | ⟨-, hadd, hmu, hlen, hΦ⟩ | ⟨hz, hΦ⟩ |
      ⟨lam, hlam, c0, hc0, hcol, hr⟩ | ⟨-, hl1, hrow, hsub, hΦ⟩
  · simp only [if_true] at hcs
    exact hmono _ (by omega) (T3 hlam T hcs hcol (by omega))
  · exact hmono _ (by omega) (T7 hadd hmu hlen T)
  · exact hmono _ (by omega) (T6 hz hh hl T)
  · simp only [if_true] at hc0
    exact hmono _ (by omega) (T4 hlam T hc0 hcol (by omega) (by omega))
  · exact hmono _ (by omega) (T8 hsub hl1 hl hrow T)

/-- **(P) Proposition 8.10** of `q_oddbox_theorem.md`: let `h ≥ 1`, `m ≥ 1`, `Λ` interlaced of
level `m` and `i ≤ 2h`. Then `V_{Λ_i} ⊆ W_{2h−i}(V_Λ)` (the slice `r − 1 − i` of the paper), as
an inclusion of subsets of `C_{m−1}`. (Proof as `Lifts.layer_subset_W`, with (P0) and (P1).) -/
theorem prop810 (hh : 1 ≤ h) {m : ℕ} (hm : 1 ≤ m) {Lam : Set Shape} (hΛ : IsInterlaced h m Lam)
    {i : ℕ} (hi : i ≤ 2 * h) :
    (VSAll F h (m - 1) (OddLayers.layerS h m Lam i) : Set (Peel.C F (2 * h + 2) (m - 1))) ⊆
      W hm (VSAll F h m Lam) (2 * h - i) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨I, hI⟩ := W_isIdeal (F := F) (q := 2 * h + 2) (by omega) hm (VSAll F h (n + 1) Lam)
    (2 * h - i) (by omega)
  have hle : VSAll F h (n + 1 - 1) (OddLayers.layerS h (n + 1) Lam i) ≤ I := by
    refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨mu, ⟨hmu, hiΦ⟩, T, rfl⟩
      have := P0 (F := F) hh hΛ (by simpa using hmu) hiΦ T
      rw [hI]
      exact this
    · rintro _ ⟨mu, ⟨hmu, hiΦ⟩, T, rfl⟩
      have := P1 (F := F) hh hΛ (by simpa using hmu) hiΦ T
      rw [hI]
      exact this
  intro x hx
  have := hle hx
  rw [← SetLike.mem_coe, hI] at this
  exact this

end OddTheorem
