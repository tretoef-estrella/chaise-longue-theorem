module

public import RequestProject.OddLayers.Layers
public import RequestProject.EvenCount.Closed

/-!
# Theorem R of `q_oddbox_layers.md` (Lemma 8.5 of the paper): the roots and their count

`Λ^{ev} = {(∅, 0)}` is `{(emptyPart, false)}` and `Λ^{od} = {((1), 0), (∅, 1)}` is
`{(onePart, false), (emptyPart, true)}`. The count of closed tuples is
`EvenCount.card_closedPointed` (Theorem (iii) of `q_even_count.md`).
-/

@[expose] public section

namespace OddLayers

open ChainLemma ChainLemma.Partition Fibres OddShapes

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- Helper for (R1) of `q_oddbox_layers.md`: `ofMultiset s = ∅` iff `s` has no positive
element. -/
lemma ofMultiset_eq_emptyPart_iff (s : Multiset ℕ) :
    ofMultiset s = emptyPart ↔ ∀ a ∈ s, ¬ 0 < a := by
  rw [← Multiset.filter_eq_nil]
  constructor
  · intro h
    have := congrArg (fun μ : Partition => (μ.parts : Multiset ℕ)) h
    simpa [ofMultiset_parts, emptyPart] using this
  · intro h
    apply Fibres.Partition.eq_of_coe_parts
    rw [ofMultiset_parts, h]
    rfl

/-- **Theorem R, (R1)** of `q_oddbox_layers.md`: for every `n ≥ 0` and `M ∈ T^n`, the shape of
`M` is `(∅, 0)` iff `cnt_M(u) = cnt_M(−u)` for every `u ∈ T` and `cnt_M(0)` is even. -/
theorem shape_eq_root_iff (S : OddSetting T h) {n : ℕ} (M : Fin n → T) :
    S.shape M = (emptyPart, false) ↔
      (∀ u, cnt M u = cnt M (S.neg u)) ∧ Even (cnt M S.zero) := by
  simp only [OddSetting.shape, Prod.mk.injEq, OddSetting.resPart, OddSetting.mark,
    ofMultiset_eq_emptyPart_iff, Multiset.forall_mem_map_iff, Finset.mem_val,
    Finset.mem_univ, true_implies, decide_eq_false_iff_not, Nat.even_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u => ?_, by omega⟩
    have a := h1 u
    have b := h1 (S.neg u)
    rw [S.neg_neg] at b
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun u => ?_, by omega⟩
    rw [h1 u]
    omega

/-- **Theorem R, proof of (R2)** of `q_oddbox_layers.md`: `T` with `u ↦ −u` and `o := 0` is a
pointed point set in the sense of `q_even_count.md` (`EvenCount.PointedSetting`), with
`|T| = 2h + 1` (if `−u = u` then `u = 0`). -/
def toPointed (S : OddSetting T h) : EvenCount.PointedSetting T h where
  neg := S.neg
  neg_neg := S.neg_neg
  o := S.zero
  neg_o := S.neg_zero
  eq_o_of_neg_eq u hu := by
    by_contra hne
    exact S.neg_ne u hne hu
  card_eq := S.card_eq

/-- **Theorem R, (R1)**, second form, of `q_oddbox_layers.md`: `Z_{Λ^{ev}}` (at any level `n`)
is the set of closed tuples of the pointed point set `T` (`EvenCount.closedPointed`). -/
theorem ZS_root_even_eq_closedPointed (S : OddSetting T h) (n : ℕ) :
    ZS S n {(emptyPart, false)} = EvenCount.closedPointed (toPointed S) n := by
  ext M
  simp only [ZS, EvenCount.closedPointed, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_singleton_iff, shape_eq_root_iff]
  rfl

/-- **Theorem R, (R2)** of `q_oddbox_layers.md`: for every `k ≥ 0`,
`|Z_{Λ^{ev}}| = Q^e_k(2h + 2)` at level `2k + 2`. -/
theorem card_ZS_root_even (S : OddSetting T h) (k : ℕ) :
    (ZS S (2 * k + 2) {(emptyPart, false)}).card = EvenCount.QkEven k (2 * h + 2) := by
  rw [ZS_root_even_eq_closedPointed, EvenCount.card_closedPointed]

/-- Helper for (R3) of `q_oddbox_layers.md`: a partition is `∅` iff it has no row. -/
lemma eq_emptyPart_iff_len (μ : Partition) : μ = emptyPart ↔ μ.len = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h
    ext1
    exact List.eq_nil_of_length_eq_zero h

/-- Helper for (R3) of `q_oddbox_layers.md`: for `ℓ(μ) ≤ h` and `1 ≤ p ≤ 2h`, the option
`opt_p(μ)` is `∅` iff `μ = (1)` and `p = 1` (only a removal can give `∅`). -/
lemma opt_eq_emptyPart_iff {μ : Partition} (hμ : μ.len ≤ h) {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 2 * h) : μ.opt (2 * h) p = emptyPart ↔ μ = onePart ∧ p = 1 := by
  have hone : onePart.len = 1 := rfl
  unfold Partition.opt
  split_ifs with h1 h2
  · constructor
    · intro he
      have hs := size_subE μ hp1 h1
      rw [he, show emptyPart.size = 0 from rfl] at hs
      have hμ1 := eq_onePart_of_size (by omega : μ.size = 1)
      subst hμ1
      exact ⟨rfl, by rw [hone] at h1; omega⟩
    · rintro ⟨rfl, rfl⟩
      exact onePart_subE_one
  · rw [eq_emptyPart_iff_len, len_addOne]
    constructor
    · intro h; omega
    · rintro ⟨rfl, rfl⟩; rw [hone] at h1; omega
  · rw [eq_emptyPart_iff_len, len_addE μ (by omega) (by omega)]
    constructor
    · intro h; omega
    · rintro ⟨rfl, rfl⟩; rw [hone] at h1; omega

open Classical in
/-- Helper for (R3) of `q_oddbox_layers.md`: `F_{{∅}}(μ) = [μ = (1)]` for `ℓ(μ) ≤ h`. -/
lemma FLam_emptyPart {μ : Partition} (hμ : μ.len ≤ h) :
    FLam h {emptyPart} μ = if μ = onePart then 1 else 0 := by
  unfold FLam
  rw [Finset.filter_congr (q := fun p => μ = onePart ∧ p = 1) (fun p hp => by
    rw [Finset.mem_Icc] at hp
    rw [Set.mem_singleton_iff]
    exact opt_eq_emptyPart_iff hμ hp.1 hp.2)]
  split_ifs with h1
  · subst h1
    have : 1 ≤ h := hμ
    rw [Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, true_and, Finset.mem_singleton]
    omega
  · simp [h1]

open Classical in
/-- **Theorem R, (R3)**, first part, of `q_oddbox_layers.md`: for every shape `(μ, δ)` with
`ℓ(μ) ≤ h`: `F_{Λ^{ev}}(μ, δ) = 1` if `(μ, δ) ∈ Λ^{od} = {((1), 0), (∅, 1)}`, and `= 0`
otherwise. -/
theorem FS_root_even (s : Shape) (hs : s.1.len ≤ h) :
    FS h {(emptyPart, false)} s =
      if s = (onePart, false) ∨ s = (emptyPart, true) then 1 else 0 := by
  obtain ⟨μ, δ⟩ := s
  simp only at hs
  have e1 : comp {(emptyPart, false)} false = {emptyPart} := by ext; simp [comp]
  have e2 : comp {(emptyPart, false)} true = ∅ := by ext; simp [comp]
  unfold FS
  cases δ with
  | false =>
    simp only [Bool.not_false, e1, e2, Set.mem_empty_iff_false, if_false, add_zero,
      FLam_emptyPart hs]
    by_cases hμ : μ = onePart <;> simp [hμ]
  | true =>
    have h0 : FLam h ∅ μ = 0 := by simp [FLam]
    simp only [Bool.not_true, e1, e2, Set.mem_singleton_iff, h0, zero_add]
    by_cases hμ : μ = emptyPart <;> simp [hμ]

/-- **Theorem R, (R3)**, second part, of `q_oddbox_layers.md`: for `h ≥ 1` and every `k ≥ 0`, at
level `m = 2k + 2`, the layer `(Λ^{ev})_0` is `Λ^{od} = {((1), 0), (∅, 1)}`. -/
theorem layerS_root_even_zero (hh : 1 ≤ h) (k : ℕ) :
    layerS h (2 * k + 2) {(emptyPart, false)} 0 = {(onePart, false), (emptyPart, true)} := by
  ext ⟨μ, δ⟩
  simp only [layerS, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hs, hpos⟩
    rw [FS_root_even _ hs.1] at hpos
    split_ifs at hpos with hc
    · exact hc
    · omega
  · intro hc
    have hsh : (μ, δ) ∈ Sh h (2 * k + 2 - 1) := by
      rcases hc with hc | hc <;> rw [hc]
      · simp [Sh, onePart, Partition.len, Partition.size]; omega
      · simp [Sh, emptyPart, Partition.len, Partition.size]
    refine ⟨hsh, ?_⟩
    rw [FS_root_even _ hsh.1, if_pos hc]
    omega

/-- **Theorem R, (R3)**, third part, of `q_oddbox_layers.md`: at level `m = 2k + 2`,
`(Λ^{ev})_i = ∅` for `i ≥ 1`. (The hypothesis `h ≥ 1` is not needed here.) -/
theorem layerS_root_even_pos (k : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    layerS h (2 * k + 2) {(emptyPart, false)} i = ∅ := by
  ext ⟨μ, δ⟩
  simp only [layerS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hs
  rw [FS_root_even _ hs.1]
  split_ifs <;> omega

/-- **Theorem R, (R4)** of `q_oddbox_layers.md`: for every `k ≥ 0`,
`|Z_{Λ^{od}}| = Q^e_k(2h + 2)` at level `2k + 1`. -/
theorem card_ZS_root_odd (S : OddSetting T h) (k : ℕ) :
    (ZS S (2 * k + 1) {(onePart, false), (emptyPart, true)}).card =
      EvenCount.QkEven k (2 * h + 2) := by
  rw [← card_ZS_root_even S k, card_ZS_eq_sum S (m := 2 * k + 2) (by omega),
    Finset.sum_range_succ',
    layerS_root_even_zero S.one_le k]
  rw [Finset.sum_eq_zero (fun i _ => by
    rw [layerS_root_even_pos k (by omega : 1 ≤ i + 1)]
    simp [ZS])]
  rw [zero_add]
  rfl

end OddLayers
