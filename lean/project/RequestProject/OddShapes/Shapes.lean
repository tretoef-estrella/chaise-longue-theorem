module

public import RequestProject.OddShapes.Lemmas

/-!
# Proposition B of `q_oddbox_shapes.md`: shapes with a mark, and the options

This file proves the description of `Sh_m` and parts (B1)–(B5) of **Proposition B** of
`q_oddbox_shapes.md`. The setting (`T`, `u ↦ −u`, `0`, `|T| = 2h + 1`) is bundled in
`S : OddSetting T h`. A tail `M' ∈ T^{m−1}` only makes sense for `m ≥ 1` (hypothesis
`hm : 1 ≤ m`), as in `RequestProject/Fibres/`.

Part (ii) of `q_P1_fibres.md` (`Fibres.multiset_resPart_consTuple_eq_opt`) is transferred
through the subtype of the non-zero elements of `T` in the proof of (B2).
-/

@[expose] public section

namespace OddShapes

open ChainLemma ChainLemma.Partition Fibres Peel

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

/-- **Part B, Setting** ("The sets `Sh_m`") of `q_oddbox_shapes.md`:
`Sh_m = {(λ, 0) : λ ∈ Par_m} ∪ {(λ, 1) : λ ∈ Par_{m−1}}`, where the second set is empty for
`m = 0` (hence the condition `1 ≤ m`). -/
theorem Sh_eq (h m : ℕ) :
    Sh h m = (fun lam => (lam, false)) '' Lifts.Par h m ∪
      (fun lam => (lam, true)) '' {lam | 1 ≤ m ∧ lam ∈ Lifts.Par h (m - 1)} := by
  ext ⟨lam, δ⟩
  cases δ <;> simp [Sh, Lifts.Par] <;> omega

/-- Membership in `Sh_m` for an unmarked shape (**Part B, Setting**, "The sets `Sh_m`", of
`q_oddbox_shapes.md`): `(λ, 0) ∈ Sh_m ↔ λ ∈ Par_m`. -/
lemma mem_Sh_false (h m : ℕ) (lam : Partition) : (lam, false) ∈ Sh h m ↔ lam ∈ Lifts.Par h m := by
  rw [Sh_eq]; simp

/-- Membership in `Sh_m` for a marked shape (**Part B, Setting**, "The sets `Sh_m`", of
`q_oddbox_shapes.md`): `(λ, 1) ∈ Sh_m ↔ m ≥ 1 ∧ λ ∈ Par_{m−1}`. -/
lemma mem_Sh_true (h m : ℕ) (lam : Partition) :
    (lam, true) ∈ Sh h m ↔ 1 ≤ m ∧ lam ∈ Lifts.Par h (m - 1) := by
  rw [Sh_eq]; simp

/-- **Proposition B, (B1)** of `q_oddbox_shapes.md`: for every `M ∈ T^m`, the shape of `M` lies
in `Sh_m`: `ℓ(λ(M)) ≤ h`, `|λ(M)| + δ(M) ≤ m` and `|λ(M)| + δ(M) ≡ m (mod 2)`. -/
theorem shape_mem_Sh (S : OddSetting T h) {m : ℕ} (M : Fin m → T) : S.shape M ∈ Sh h m := by
  obtain ⟨k, N, hN, hk⟩ := S.exists_subTuple m M
  have hR := S.resPart_eq_sub M N hN
  have h1 := resPart_len_le_and_size_mod S.sub N
  have h2 := size_resPart_le S.sub N
  simp only [Sh, OddSetting.shape, OddSetting.mark, Set.mem_setOf_eq, hR]
  refine ⟨h1.1, ?_, ?_⟩ <;> by_cases hz : cnt M S.zero % 2 = 1 <;> simp [hz] <;> omega

/-- Helper for (B2) of `q_oddbox_shapes.md`: the non-zero elements of `T`, as a multiset. -/
lemma filter_ne_zero_val (S : OddSetting T h) :
    (Finset.univ.filter (· ≠ S.zero)).val =
      (Finset.univ : Finset {u : T // u ≠ S.zero}).val.map Subtype.val := by
  rw [Finset.filter_val, S.univ_val_eq, Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_eq_self.mpr]
  intro a ha
  obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
  exact v.2

/-- **Proposition B, (B2)**, precise form, the value `t = 0`, of `q_oddbox_shapes.md`: if `M'` has
shape `(μ, δ)`, then `(0, M')` has shape `(μ, 1 − δ)`. -/
theorem shape_consTuple_zero (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (M' : Fin (m - 1) → T) :
    S.shape (consTuple (m := m) S.zero M') = ((S.shape M').1, !(S.shape M').2) := by
  simp only [OddSetting.shape, Prod.mk.injEq]
  constructor
  · unfold OddSetting.resPart
    congr 1
    apply Multiset.map_congr rfl
    intro u _
    rw [cnt_consTuple hm, cnt_consTuple hm]
    by_cases hu : u = S.zero
    · subst hu; simp [S.neg_zero]
    · have : S.zero ≠ S.neg u := fun e => S.neg_ne_zero hu e.symm
      simp [Ne.symm hu, this]
  · unfold OddSetting.mark
    rw [cnt_consTuple hm, if_pos rfl]
    by_cases hz : cnt M' S.zero % 2 = 1
    · simp only [hz, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
    · simp only [hz, decide_false, Bool.not_false, decide_eq_true_eq]; omega

/-- Helper for (B2) of `q_oddbox_shapes.md`: for `t ≠ 0`, the shape of `(t, M')` is
`(λ', δ(M'))`, where `λ'` is the residue partition (in the sense of `q_P1_fibres.md`, on the
non-zero elements) of `(t, N)`, `N` being a non-zero part of `M'`. -/
lemma shape_consTuple_ne (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) {t : T} (ht : t ≠ S.zero)
    (M' : Fin (m - 1) → T) {k : ℕ} (N : Fin k → {u : T // u ≠ S.zero})
    (hN : ∀ v, cnt N v = cnt M' v.1) :
    S.shape (consTuple (m := m) t M') =
      (S.sub.resPart (consTuple (m := k + 1) ⟨t, ht⟩ N), (S.shape M').2) := by
  simp only [OddSetting.shape, Prod.mk.injEq]
  constructor
  · apply S.resPart_eq_sub
    intro v
    rw [cnt_consTuple_succ, cnt_consTuple hm, hN]
    simp [Subtype.ext_iff]
  · unfold OddSetting.mark
    rw [cnt_consTuple hm, if_neg ht, add_zero]

/-- **Proposition B, (B2)**, precise form, the values `t ≠ 0`, of `q_oddbox_shapes.md`: if `M'`
has shape `(μ, δ)`, the `2h` values `t ≠ 0` give the multiset
`{(opt_p(μ), δ) : p = 1, …, 2h}` of shapes of `(t, M')` (with `L = 2h`). -/
theorem multiset_shape_consTuple_ne_zero (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (M' : Fin (m - 1) → T) :
    (Finset.univ.filter (· ≠ S.zero)).val.map (fun t => S.shape (consTuple (m := m) t M')) =
      (Finset.Icc 1 (2 * h)).val.map
        (fun p => ((S.shape M').1.opt (2 * h) p, (S.shape M').2)) := by
  obtain ⟨k, N, hN, -⟩ := S.exists_subTuple (m - 1) M'
  rw [filter_ne_zero_val, Multiset.map_map]
  rw [Multiset.map_congr rfl
    (g := fun v => (S.sub.resPart (consTuple (m := k + 1) v N), (S.shape M').2))]
  · have e := congrArg (Multiset.map (fun x => (x, (S.shape M').2)))
      (multiset_resPart_consTuple_eq_opt S.sub (m := k + 1) (by omega) N)
    simp only [Multiset.map_map, Function.comp_def] at e
    rw [e, ← S.resPart_eq_sub M' N hN]
    rfl
  · intro v _
    exact shape_consTuple_ne S hm v.2 M' N hN

/-- **Proposition B, (B2) (options; Lemma 8.1 of the paper)** of `q_oddbox_shapes.md`: for
`m ≥ 1` and `M' ∈ T^{m−1}` with shape `(μ, δ)`, the multiset `{shape of (t, M') : t ∈ T}` (one
entry for each of the `2h + 1` elements `t`) equals the multiset
`{optS_p(μ, δ) : p = 1, …, 2h + 1}`. -/
theorem multiset_shape_consTuple_eq_optS (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m)
    (M' : Fin (m - 1) → T) :
    Finset.univ.val.map (fun t => S.shape (consTuple (m := m) t M')) =
      (Finset.Icc 1 (2 * h + 1)).val.map (optS h (S.shape M')) := by
  have hlen : (S.shape M').1.len ≤ h := (shape_mem_Sh S M').1
  have hval : (Finset.univ : Finset T).val = S.zero ::ₘ (Finset.univ.filter (· ≠ S.zero)).val := by
    rw [filter_ne_zero_val, S.univ_val_eq]
  rw [hval, Multiset.map_cons, multiset_shape_consTuple_ne_zero S hm, shape_consTuple_zero S hm]
  generalize S.shape M' = s at hlen ⊢
  obtain ⟨μ, δ⟩ := s
  rw [map_optS h μ δ (by simp only at hlen; omega)]

/-- **Proposition B, (B3)** of `q_oddbox_shapes.md`: if `(μ, δ) ∈ Sh_{m−1}` (`m ≥ 1`), then
`optS_p(μ, δ) ∈ Sh_m` for every `p = 1, …, 2h + 1`. -/
theorem optS_mem_Sh {m : ℕ} (hm : 1 ≤ m) {μ : Partition} {δ : Bool} (hs : (μ, δ) ∈ Sh h (m - 1))
    {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ 2 * h + 1) : optS h (μ, δ) p ∈ Sh h m := by
  unfold optS
  simp only
  split_ifs with h1 h2 h3
  · have e1 := size_subE μ hp1 h1
    have e2 := len_subE_le μ hp1 h1
    cases δ <;> simp [Sh] at hs ⊢ <;> omega
  · cases δ <;> simp [Sh] at hs ⊢ <;> omega
  · have e1 := Fibres.size_addOne μ
    have e2 := len_addOne μ
    cases δ <;> simp [Sh] at hs ⊢ <;> omega
  · have e1 := size_addE μ (j := 2 * h + 2 - p) (by omega) (by omega)
    have e2 := len_addE μ (j := 2 * h + 2 - p) (by omega) (by omega)
    cases δ <;> simp [Sh] at hs ⊢ <;> omega

open Classical in
/-- **Proposition B, (B5)** of `q_oddbox_shapes.md`:
`F_Λ(μ, δ) = #{p ∈ {1, …, 2h + 1} : optS_p(μ, δ) ∈ Λ}` whenever `ℓ(μ) ≤ h`. -/
theorem FS_eq_card (h : ℕ) (Λ : Set Shape) (μ : Partition) (δ : Bool) (hℓ : μ.len ≤ h) :
    FS h Λ (μ, δ) = ((Finset.Icc 1 (2 * h + 1)).filter fun p => optS h (μ, δ) p ∈ Λ).card := by
  have e1 : ((Finset.Icc 1 (2 * h + 1)).filter fun p => optS h (μ, δ) p ∈ Λ).card =
      (((Finset.Icc 1 (2 * h + 1)).val.map (optS h (μ, δ))).filter (· ∈ Λ)).card := by
    rw [Multiset.filter_map, Multiset.card_map]
    rfl
  rw [e1, map_optS h μ δ (by omega), Multiset.filter_cons, Multiset.card_add, Multiset.filter_map,
    Multiset.card_map]
  unfold FS FLam
  simp only [comp, Set.mem_setOf_eq]
  rw [add_comm]
  congr 1
  split_ifs <;> simp

open Classical in
/-- **Proposition B, (B4)** of `q_oddbox_shapes.md`, first form: for every set `Λ` of shapes,
every `m ≥ 1` and every tail `M' ∈ T^{m−1}`,
`#{t ∈ T : the shape of (t, M') lies in Λ} = F_Λ(shape of M')`. -/
theorem card_shape_consTuple_mem (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Shape)
    (M' : Fin (m - 1) → T) :
    (Finset.univ.filter fun t => S.shape (consTuple (m := m) t M') ∈ Λ).card =
      FS h Λ (S.shape M') := by
  have h2 := congrArg (fun s => (s.filter (· ∈ Λ)).card)
    (multiset_shape_consTuple_eq_optS S hm M')
  simp only [Multiset.filter_map, Multiset.card_map] at h2
  rw [show S.shape M' = ((S.shape M').1, (S.shape M').2) from rfl,
    FS_eq_card h Λ _ _ (shape_mem_Sh S M').1]
  exact h2

open Classical in
/-- **Proposition B, (B4)** of `q_oddbox_shapes.md`, second form: in the notation of
`q_peeling_lemma.md`, with `Z = Z_Λ`, `|F(M')| = F_Λ(shape of M')`. -/
theorem card_fiber_ZS (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Shape)
    (M' : Fin (m - 1) → T) :
    (fiber (ZS S m Λ) M').card = FS h Λ (S.shape M') := by
  rw [← card_shape_consTuple_mem S hm Λ M']
  congr 1
  ext t
  simp [fiber, ZS]

open Classical in
/-- **Proposition B, (B4)** of `q_oddbox_shapes.md`, third form: with `Z = Z_Λ`,
`Z_{>i} = {M' ∈ T^{m−1} : F_Λ(shape of M') > i}` for every `i ≥ 0`. -/
theorem Zgt_ZS (S : OddSetting T h) {m : ℕ} (hm : 1 ≤ m) (Λ : Set Shape) (i : ℕ) :
    Zgt (ZS S m Λ) i = Finset.univ.filter fun M' => i < FS h Λ (S.shape M') := by
  ext M'
  simp [Zgt, card_fiber_ZS S hm Λ M']

end OddShapes
