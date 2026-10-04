module

public import RequestProject.OddShapes.Shapes

/-!
# Part C of `q_oddbox_shapes.md`: interlaced pairs and the chain

This file proves **Lemma C (chain; Lemma 8.3 of the paper)** of `q_oddbox_shapes.md`, parts
(C1), (C2) and (C3). The **Definition (interlaced pair)** is `OddShapes.IsInterlaced`
(in `RequestProject/OddShapes/Defs.lean`).
-/

@[expose] public section

namespace OddShapes

open ChainLemma ChainLemma.Partition Fibres

/-- **Lemma C, (C1)** of `q_oddbox_shapes.md`: for every `(ν, δ) ∈ Sh_m` and `1 ≤ j ≤ ℓ(ν)`,
`(ν − e_j, 1 − δ) ∈ Sh_m`. -/
theorem subE_mem_Sh {h m : ℕ} {ν : Partition} {δ : Bool} (hs : (ν, δ) ∈ Sh h m) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ ν.len) : (ν.subE j, !δ) ∈ Sh h m := by
  have e1 := size_subE ν hj1 hj
  have e2 := len_subE_le ν hj1 hj
  cases δ <;> simp [Sh] at hs ⊢ <;> omega

/-- Helper for (C2) of `q_oddbox_shapes.md`: by (D1), each component `Λ^δ` of an interlaced pair
is a down-set (of `Par_m` or `Par_{m−1}`); so if `(x, δ) ∈ Sh_m`, `x ≼ y` and `(y, δ) ∈ Λ`, then
`(x, δ) ∈ Λ`. -/
lemma IsInterlaced.down {h m : ℕ} {Λ : Set Shape} (hΛ : IsInterlaced h m Λ) {x y : Partition}
    {δ : Bool} (hx : (x, δ) ∈ Sh h m) (hxy : x ≼ y) (hy : (y, δ) ∈ Λ) : (x, δ) ∈ Λ := by
  obtain ⟨-, ⟨h0, h1⟩, -⟩ := hΛ
  cases δ
  · exact h0.2 x y ((mem_Sh_false h m x).mp hx) hxy hy
  · exact h1.2 x y ((mem_Sh_true h m x).mp hx).2 hxy hy

/-- **Lemma C, (C2)**, step form, of `q_oddbox_shapes.md`: let `m ≥ 1`, let `Λ` be an interlaced
pair of level `m` and `(μ, δ) ∈ Sh_{m−1}`. For `1 ≤ p ≤ 2h`, if `optS_{p+1}(μ, δ) ∈ Λ` then
`optS_p(μ, δ) ∈ Λ`. -/
theorem optS_mem_of_succ {h m : ℕ} (hm : 1 ≤ m) {Λ : Set Shape} (hΛ : IsInterlaced h m Λ)
    {μ : Partition} {δ : Bool} (hs : (μ, δ) ∈ Sh h (m - 1)) {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 2 * h) (hmem : optS h (μ, δ) (p + 1) ∈ Λ) : optS h (μ, δ) p ∈ Λ := by
  have hl : μ.len ≤ h := hs.1
  have hSh := optS_mem_Sh hm hs hp1 (by omega)
  rcases lt_trichotomy p μ.len with hlt | heq | hgt
  · -- two removals: `μ − e_p ≼ μ − e_{p+1}`
    rw [optS_of_le h μ δ (by omega)] at hmem
    rw [optS_of_le h μ δ (by omega)] at hSh ⊢
    exact hΛ.down hSh (opt_le_opt_succ μ (2 * h) p (by omega) hp1 (by omega)) hmem
  · -- `p = ℓ`: (D2) applied to `(μ, 1 − δ)` and the row `ℓ`
    subst heq
    rw [optS_len_succ] at hmem
    rw [optS_of_le h μ δ le_rfl]
    have := hΛ.2.2 μ (!δ) hmem μ.len hp1 le_rfl
    simpa [Partition.opt] using this
  · by_cases hq : p = μ.len + 1
    · subst hq
      rw [optS_len_succ]
      rw [optS_of_ge h μ δ (by omega)] at hmem
      by_cases hc : μ.len + 1 ≤ 2 * h - μ.len
      · -- `s_{p+1} = (μ ⊔ 1, δ)`: (D2) applied to its last row `ℓ + 1`
        simp only [Partition.opt, show ¬ μ.len + 1 + 1 - 1 ≤ μ.len by omega,
          show μ.len + 1 + 1 - 1 ≤ 2 * h - μ.len by omega, if_true, if_false] at hmem
        have := hΛ.2.2 μ.addOne δ hmem (μ.len + 1) (by omega) (by rw [len_addOne])
        rwa [addOne_subE] at this
      · -- `ℓ = h` and `s_{p+1} = (μ + e_ℓ, δ)`: (D2) applied to the row where the box was added
        simp only [Partition.opt, show ¬ μ.len + 1 + 1 - 1 ≤ μ.len by omega,
          show ¬ μ.len + 1 + 1 - 1 ≤ 2 * h - μ.len by omega, if_false,
          show 2 * h + 1 - (μ.len + 1 + 1 - 1) = μ.len by omega] at hmem
        obtain ⟨j', h1, h2, h3⟩ := exists_addE_subE μ (j := μ.len) (by omega) le_rfl
        have := hΛ.2.2 _ δ hmem j' h1 h2
        rwa [h3] at this
    · -- `p ≥ ℓ + 2`: `opt_{p−1}(μ) ≼ opt_p(μ)`
      rw [optS_of_ge h μ δ (by omega)] at hmem hSh ⊢
      rw [show p + 1 - 1 = (p - 1) + 1 by omega] at hmem
      exact hΛ.down hSh (opt_le_opt_succ μ (2 * h) (p - 1) (by omega) (by omega) (by omega)) hmem

/-- Helper for (C2) of `q_oddbox_shapes.md`: a subset of `{1, …, N}` that is closed under
`p + 1 ↦ p` is the initial segment `{1, …, F}` with `F` its number of elements. -/
lemma filter_Icc_eq_Icc_card (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hstep : ∀ p, 1 ≤ p → p < N → P (p + 1) → P p) :
    (Finset.Icc 1 N).filter P = Finset.Icc 1 ((Finset.Icc 1 N).filter P).card := by
  set A := (Finset.Icc 1 N).filter P with hA
  have hdown : ∀ d p', p' + d ∈ A → 1 ≤ p' → p' ∈ A := by
    intro d
    induction d with
    | zero => intro p' hp _; simpa using hp
    | succ d ih =>
      intro p' hp hp'
      have h1 := ih (p' + 1) (by rwa [show p' + 1 + d = p' + (d + 1) by omega]) (by omega)
      simp only [hA, Finset.mem_filter, Finset.mem_Icc] at h1 ⊢
      exact ⟨⟨hp', by omega⟩, hstep p' hp' (by omega) h1.2⟩
  have hsub : A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hAeq : A = Finset.Icc 1 (A.sup id) := by
    ext p
    simp only [Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨(Finset.mem_Icc.1 (hsub hp)).1, Finset.le_sup (f := id) hp⟩
    · rintro ⟨hp1, hp2⟩
      rcases A.eq_empty_or_nonempty with hAe | hAne
      · simp [hAe] at hp2; omega
      · obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup A hAne id
        exact hdown (q - p) p (by rwa [show p + (q - p) = q by simp [hmax] at hp2; omega]) hp1
  conv_rhs => rw [hAeq]
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact hAeq

open Classical in
/-- **Lemma C, (C2) (chain; Lemma 8.3 of the paper)** of `q_oddbox_shapes.md`: let `m ≥ 1`, let
`Λ` be an interlaced pair of level `m`, and let `(μ, δ) ∈ Sh_{m−1}`. Then
`{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) ∈ Λ}` is the initial segment `{1, …, F_Λ(μ, δ)}`. -/
theorem optS_filter_eq_Icc {h m : ℕ} (hm : 1 ≤ m) {Λ : Set Shape} (hΛ : IsInterlaced h m Λ)
    {μ : Partition} {δ : Bool} (hs : (μ, δ) ∈ Sh h (m - 1)) :
    (Finset.Icc 1 (2 * h + 1)).filter (fun p => optS h (μ, δ) p ∈ Λ) =
      Finset.Icc 1 (FS h Λ (μ, δ)) := by
  rw [FS_eq_card h Λ μ δ hs.1]
  exact filter_Icc_eq_Icc_card _ _
    (fun p hp1 hp hmem => optS_mem_of_succ hm hΛ hs hp1 (by omega) hmem)

/-! ### (C3): four examples -/

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: the empty partition `∅`. -/
def emptyPart : Partition := ⟨[], List.Pairwise.nil, by simp⟩

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: the partition `(1)` with one part equal to `1`. -/
def onePart : Partition := ⟨[1], by simp, by simp⟩

/-- Helper for (C3) of `q_oddbox_shapes.md`: every `λ ≼ ∅` is `∅`. -/
lemma eq_emptyPart_of_le {lam : Partition} (hle : lam ≼ emptyPart) : lam = emptyPart := by
  have h1 := hle 1 le_rfl
  simp only [Partition.S, Finset.Icc_self, Finset.sum_singleton] at h1
  have h2 : emptyPart.row 1 = 0 := rfl
  have hlen : lam.len = 0 := by
    by_contra hne
    have := row_pos lam 1 le_rfl (by omega)
    omega
  ext1
  exact List.eq_nil_of_length_eq_zero hlen

/-- Helper for (C3) of `q_oddbox_shapes.md`: a partition with positive entries summing to `1`
is `(1)`. -/
lemma eq_onePart_of_size {lam : Partition} (hs : lam.size = 1) : lam = onePart := by
  have hpos := lam.pos
  ext1
  unfold Partition.size at hs
  show lam.parts = [1]
  match hl : lam.parts with
  | [] => rw [hl] at hs; simp at hs
  | [a] => rw [hl] at hs; simp at hs; rw [hs]
  | a :: b :: l =>
    rw [hl] at hs hpos
    have ha := hpos a (by simp)
    have hb := hpos b (by simp)
    simp at hs
    omega

/-- Helper for (C3) of `q_oddbox_shapes.md`: a partition `λ ≼ (1)` with `|λ|` odd is `(1)`. -/
lemma eq_onePart_of_le {lam : Partition} (hle : lam ≼ onePart) (hodd : lam.size % 2 = 1) :
    lam = onePart := by
  apply eq_onePart_of_size
  have hlen : 1 ≤ lam.len := by
    by_contra h0
    have : lam.parts = [] := List.eq_nil_of_length_eq_zero (by unfold Partition.len at h0; omega)
    simp [Partition.size, this] at hodd
  have h1 := hle lam.len hlen
  rw [S_eq_sum_take, S_eq_sum_take, List.take_of_length_le (by rfl)] at h1
  have h2 : (onePart.parts.take lam.len).sum ≤ 1 := by
    obtain ⟨n, hn⟩ : ∃ n, lam.len = n + 1 := ⟨lam.len - 1, by omega⟩
    rw [hn]
    simp [onePart]
  unfold Partition.size at hodd ⊢
  omega

/-- Helper for (C3) of `q_oddbox_shapes.md`: `(1) − e_1 = ∅`. -/
lemma onePart_subE_one : onePart.subE 1 = emptyPart := by
  ext1
  simp [Partition.subE, onePart, emptyPart, sortDesc]

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: the empty set is an interlaced pair of every
level. -/
theorem isInterlaced_empty (h m : ℕ) : IsInterlaced h m ∅ := by
  refine ⟨Set.empty_subset _, ⟨⟨fun x hx => ?_, fun _ μ _ _ hμ => ?_⟩,
    ⟨fun x hx => ?_, fun _ μ _ _ hμ => ?_⟩⟩, fun ν δ hν => ?_⟩
  · simp [comp] at hx
  · simp [comp] at hμ
  · simp [comp] at hx
  · simp [comp] at hμ
  · simp at hν

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: `Sh_m` is an interlaced pair of level `m`. -/
theorem isInterlaced_Sh (h m : ℕ) : IsInterlaced h m (Sh h m) := by
  refine ⟨subset_rfl, ⟨⟨fun x hx => (mem_Sh_false h m x).mp hx,
    fun lam _ hl _ _ => (mem_Sh_false h m lam).mpr hl⟩,
    ⟨fun x hx => ((mem_Sh_true h m x).mp hx).2,
    fun lam _ hl _ hμ => (mem_Sh_true h m lam).mpr ⟨((mem_Sh_true h m _).mp hμ).1, hl⟩⟩⟩,
    fun ν δ hν j hj1 hj => subE_mem_Sh hν hj1 hj⟩

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: `{(∅, 0)}` is an interlaced pair of every even
level `m`. -/
theorem isInterlaced_root_even (h m : ℕ) (hm : Even m) :
    IsInterlaced h m {(emptyPart, false)} := by
  have hm2 : m % 2 = 0 := Nat.even_iff.mp hm
  have hpar : emptyPart ∈ Lifts.Par h m := by
    simp [Lifts.Par, emptyPart, Partition.size, Partition.len, hm2]
  refine ⟨?_, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (mem_Sh_false h m _).mpr hpar
  · intro x hx
    simp only [comp, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq, and_true] at hx
    rw [hx]; exact hpar
  · intro lam μ _ hle hμ
    simp only [comp, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq, and_true] at hμ ⊢
    subst hμ
    exact eq_emptyPart_of_le hle
  · intro x hx; simp [comp] at hx
  · intro _ μ _ _ hμ; simp [comp] at hμ
  · intro ν δ hν j hj1 hj
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hν
    rw [hν.1] at hj
    simp [emptyPart, Partition.len] at hj
    omega

/-- **Lemma C, (C3)** of `q_oddbox_shapes.md`: `{((1), 0), (∅, 1)}` is an interlaced pair of
every odd level `m`. (Here `h ≥ 1`, as in the setting of Part B, is needed for `ℓ((1)) ≤ h`.) -/
theorem isInterlaced_root_odd (h m : ℕ) (hh : 1 ≤ h) (hm : Odd m) :
    IsInterlaced h m {(onePart, false), (emptyPart, true)} := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hm1 : 1 ≤ m := hm.pos
  have hpar1 : onePart ∈ Lifts.Par h m := by
    simp only [Lifts.Par, onePart, Partition.size, Partition.len, Set.mem_setOf_eq]
    simp; omega
  have hpar0 : emptyPart ∈ Lifts.Par h (m - 1) := by
    simp only [Lifts.Par, emptyPart, Partition.size, Partition.len, Set.mem_setOf_eq]
    simp; omega
  refine ⟨?_, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact (mem_Sh_false h m _).mpr hpar1
    · exact (mem_Sh_true h m _).mpr ⟨hm1, hpar0⟩
  · intro x hx
    simp [comp] at hx
    rw [hx]; exact hpar1
  · intro lam μ hl hle hμ
    simp [comp] at hμ ⊢
    subst hμ
    exact eq_onePart_of_le hle (by have := hl.2.1; omega)
  · intro x hx
    simp [comp] at hx
    rw [hx]; exact hpar0
  · intro lam μ _ hle hμ
    simp [comp] at hμ ⊢
    subst hμ
    exact eq_emptyPart_of_le hle
  · intro ν δ hν j hj1 hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hν
    rcases hν with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hj' : j = 1 := by simp [onePart, Partition.len] at hj; omega
      subst hj'
      rw [onePart_subE_one]
      simp
    · simp [emptyPart, Partition.len] at hj
      omega

end OddShapes
