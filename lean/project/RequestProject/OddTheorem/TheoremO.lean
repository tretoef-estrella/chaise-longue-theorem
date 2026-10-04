module

public import RequestProject.OddTheorem.Theorem811
public import RequestProject.TheoremB.Main
public import RequestProject.EvenCount.Main

/-!
# Part O of `q_oddbox_theorem.md`: Theorem O, the inequality `≥`

This file formalizes **(O) Theorem O (`≥`)** of `q_oddbox_theorem.md`:
`Q^e_k(2h + 2) ≤ dim_F 𝔇_k` for every field `F`, `h ≥ 1` and `k`.
-/

@[expose] public section

namespace OddTheorem

open Peel hiding C
open Tight ChainLemma OddShapes OddPatterns OddLifts OddLifts2

set_option synthInstance.maxHeartbeats 200000

/-- Auxiliary for **(O)** of `q_oddbox_theorem.md` (the `OddSetting` built in its proof):
`T = Option (Fin h × Bool)` with the zero `none` and the involution `(u, ε) ↦ (u, !ε)`;
it has `|T| = 2h + 1`. -/
def stdOddSetting (h : ℕ) (hh : 1 ≤ h) : OddSetting (Option (Fin h × Bool)) h where
  neg := Option.map (fun p => (p.1, !p.2))
  zero := none
  neg_neg := by intro u; cases u <;> simp
  neg_zero := rfl
  neg_ne := by
    intro u hu
    cases u with
    | none => exact absurd rfl hu
    | some p => simp [Prod.ext_iff]
  one_le := hh
  card_eq := by simp [Fintype.card_option]; ring

/-- Auxiliary for **(O)** of `q_oddbox_theorem.md`: `onePart = TheoremB.one` and
`∅ ⊔ 1 = (1)`. -/
theorem emptyPart_addOne : emptyPart.addOne = TheoremB.one := rfl

/-- Auxiliary for **(O)** of `q_oddbox_theorem.md` (the marked part): every marked pattern of `∅`
on `Fin (2k+1)` has its product in `𝔇_k = TheoremB.DIdeal F (2h+2) k`. Its product is
`markedPf F h 0 B_0 · D_P`; by `OddPatterns.D3` (`l = 0`, needs `1 ≤ h`),
`markedPf F h 0 B_0 ∈ Membership.UB (2h+1) 1 y B_0`, and each generator `vand y {s} · D_Q`, times
`D_P`, is the product of a tight pattern of `(1) = TheoremB.one` (`OddLifts2.exists_tpattern_addOne`
with `μ = ∅`), which lies in `𝔇_k` by `TheoremB.VLamAll_one_eq`. -/
theorem marked_emptyPart_mem_DIdeal (F : Type*) [Field F] {h : ℕ} (hh : 1 ≤ h) (k : ℕ)
    (T : MarkedPattern emptyPart (Finset.univ : Finset (Fin (2 * k + 1)))) :
    T.prod F h ∈ TheoremB.DIdeal F (2 * h + 2) k := by
  classical
  set G' : Peel.C F (2 * h + 2) (2 * k + 1) := (∏ e ∈ T.pairs, pairD F (2 * h + 2) e) *
    ∏ c ∈ Finset.Icc 2 1, Delta F (2 * h + 2) (cleanMBlocks T c) with hG'
  have hG : T.prod F h = markedPf F h emptyPart.len T.marked * G' :=
    prod_eq_markedPf_mul T (N := 1) (by decide)
  rw [← TheoremB.VLamAll_one_eq]
  have key : ∀ g ∈ Membership.UB (2 * h + 1) (emptyPart.len + 1) (y F (2 * h + 2)) T.marked,
      g * G' ∈ VLamAll F (2 * h + 2) (2 * k + 1) {TheoremB.one} := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, Q, hS, hScard, hQ, hQs, rfl⟩ := hx
      obtain ⟨T', hT'⟩ := exists_tpattern_addOne (F := F) (h := h) T S Q hS hScard hQ hQs
        (N := 1) (by decide) (by decide) le_rfl
      have hmem : T'.prod F (2 * h + 2) ∈ VLamAll F (2 * h + 2) (2 * k + 1) {TheoremB.one} :=
        Ideal.subset_span ⟨_, by rw [emptyPart_addOne]; rfl, T', rfl⟩
      rw [hT'] at hmem
      have e : vand (y F (2 * h + 2)) S * Membership.DPy (2 * h + 1) (y F (2 * h + 2)) Q * G' =
          Delta F (2 * h + 2) S * (∏ e ∈ Q, pairD F (2 * h + 2) e) * G' := rfl
      rw [e]
      exact hmem
    | zero => rw [zero_mul]; exact Ideal.zero_mem _
    | add x z _ _ hx hz => rw [add_mul]; exact Ideal.add_mem _ hx hz
    | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ a hx
  obtain ⟨t, ht⟩ := T.marked_card
  rw [hG]
  exact key _ (D3 (F := F) hh emptyPart.len T.marked t ht)

/-- Auxiliary for **(O)** of `q_oddbox_theorem.md`:
`V_{Λroot} ≤ 𝔇_k` for `Λroot = {((1), false), (∅, true)}` at level `2k + 1`. The tight part is
`Tight.VLamAll F (2h+2) (2k+1) {TheoremB.one} = 𝔇_k` (`TheoremB.VLamAll_one_eq`); the marked part
is `marked_emptyPart_mem_DIdeal`. -/
theorem VSAll_root_le_DIdeal (F : Type*) [Field F] {h : ℕ} (hh : 1 ≤ h) (k : ℕ) :
    VSAll F h (2 * k + 1) {(onePart, false), (emptyPart, true)} ≤
      TheoremB.DIdeal F (2 * h + 2) k := by
  refine sup_le ?_ (Ideal.span_le.2 ?_)
  · have hc : comp {(onePart, false), (emptyPart, true)} false = {TheoremB.one} := by
      ext lam; simp [comp]; rfl
    rw [hc, ← TheoremB.VLamAll_one_eq]
    exact le_rfl
  · rintro _ ⟨lam, hlam, T, rfl⟩
    have hl : lam = emptyPart := by simpa [comp] using hlam
    subst hl
    exact marked_emptyPart_mem_DIdeal F hh k T

/-- **(O) Theorem O (`≥`)** of `q_oddbox_theorem.md`: for every field `F`, every `h ≥ 1` and every
`k`, `Q^e_k(2h + 2) ≤ dim_F 𝔇_k`, where `𝔇_k = TheoremB.DIdeal F (2h+2) k`. (Proof:
`Λroot = {((1), false), (∅, true)}` is interlaced of level `2k + 1`
(`OddShapes.isInterlaced_root_odd`), `|Z_{Λroot}| = Q^e_k(2h+2)` (`OddLayers.card_ZS_root_odd`,
for the setting `stdOddSetting`), Theorem 8.11, and `V_{Λroot} ≤ 𝔇_k`.) -/
theorem theoremO (F : Type*) [Field F] {h : ℕ} (hh : 1 ≤ h) (k : ℕ) :
    EvenCount.QkEven k (2 * h + 2) ≤
      Module.finrank F ((TheoremB.DIdeal F (2 * h + 2) k).restrictScalars F) := by
  classical
  rw [← OddLayers.card_ZS_root_odd (stdOddSetting h hh) k]
  refine (theorem811 F (stdOddSetting h hh) (2 * k + 1) _
    (isInterlaced_root_odd h (2 * k + 1) hh (by simp))).trans ?_
  exact Submodule.finrank_mono (fun x hx => VSAll_root_le_DIdeal F hh k hx)

end OddTheorem
