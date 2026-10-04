module

public import RequestProject.OddLayers.Rows

/-!
# (E) and (L2) of Theorem L of `q_oddbox_layers.md`

The proof of (E) follows the case analysis of the file (removals, the switch of the mark, the
middle positions, additions). Every equality of partitions in it is proved through the multisets
of parts (`subE_eq`, `addE_eq`, `addOne_eq`); the rows `j*`, `p*`, `i_0` of the file are the rows
`cge`/`cgt` of `RequestProject/OddLayers/Rows.lean` (last and first rows of a given value).
The proof of (L2) goes through (E) and the chain (C2) (`optS_filter_eq_Icc`) for the two shapes
`(ν, δ)` and `(ν − e_j, 1 − δ)`.
-/

@[expose] public section

namespace OddLayers

open ChainLemma ChainLemma.Partition Fibres OddShapes

/-- Helper for (E) of `q_oddbox_layers.md`: the counts of the parts after lowering a part `x`. -/
lemma count_lower (s : Multiset ℕ) (x b : ℕ) :
    ((s.erase x + {x - 1}).filter (0 < ·)).count b =
      if 0 < b then s.count b - (if b = x then 1 else 0) + (if b = x - 1 then 1 else 0)
      else 0 := by
  rw [Multiset.count_filter, Multiset.count_add, count_erase', Multiset.count_singleton]

/-- Helper for (E) of `q_oddbox_layers.md`: the counts of the parts after raising a part `x`. -/
lemma count_raise (s : Multiset ℕ) (x b : ℕ) :
    ((s.erase x + {x + 1}).filter (0 < ·)).count b =
      if 0 < b then s.count b - (if b = x then 1 else 0) + (if b = x + 1 then 1 else 0)
      else 0 := by
  rw [Multiset.count_filter, Multiset.count_add, count_erase', Multiset.count_singleton]

/-- Helper for (E) of `q_oddbox_layers.md`: the counts of the parts after adding a part `1`. -/
lemma count_addOne (s : Multiset ℕ) (b : ℕ) :
    ((s + {1}).filter (0 < ·)).count b =
      if 0 < b then s.count b + (if b = 1 then 1 else 0) else 0 := by
  rw [Multiset.count_filter, Multiset.count_add, Multiset.count_singleton]

/-- Helper for (E) of `q_oddbox_layers.md`: the number of parts satisfying a predicate `q`
(which only holds for positive numbers) after lowering a part `a`. -/
lemma card_filter_lower (P : Multiset ℕ) {a : ℕ} (ha : a ∈ P) (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ b, q b → 0 < b) :
    Multiset.card (((P.erase a + {a - 1}).filter (0 < ·)).filter q) + (if q a then 1 else 0) =
      Multiset.card (P.filter q) + (if q (a - 1) then 1 else 0) := by
  rw [Multiset.filter_filter, Multiset.filter_congr (q := q) (fun b _ => ⟨fun h => h.1,
    fun h => ⟨h, hq b h⟩⟩), Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton,
    ← card_filter_erase P q ha]
  split_ifs <;> simp

/-- **(D2)** of `q_oddbox_shapes.md` in the form used in the proof of (E) of
`q_oddbox_layers.md`: if `(κ, ε) ∈ Λ` and `x` is a part of `κ`, then lowering one part `x` of `κ`
(and re-sorting) and switching the mark gives a shape of `Λ`. -/
lemma lower_mem {h m : ℕ} {Λ : Set Shape} (hΛ : IsInterlaced h m Λ) {κ : Partition}
    {ε : Bool} (hκ : (κ, ε) ∈ Λ) {x : ℕ} (hx : x ∈ pm κ) :
    ∃ κ', pm κ' = ((pm κ).erase x + {x - 1}).filter (0 < ·) ∧ (κ', !ε) ∈ Λ := by
  obtain ⟨h1, h2, h3⟩ := row_cge κ hx
  refine ⟨κ.subE (cge κ x), ?_, hΛ.2.2 κ ε hκ _ h1 h2⟩
  rw [pm_subE κ h1 h2, h3]

/-- The removal positions of `optS` (**Part B, Setting**, of `q_oddbox_shapes.md`). -/
lemma optS_rem (h : ℕ) (μ : Partition) (δ : Bool) {p : ℕ} (hp : p ≤ μ.len) :
    optS h (μ, δ) p = (μ.subE p, δ) := by
  simp [optS, hp]

/-- The middle positions of `optS` (**Part B, Setting**, of `q_oddbox_shapes.md`). -/
lemma optS_mid (h : ℕ) (μ : Partition) (δ : Bool) {p : ℕ} (hp1 : μ.len + 1 < p)
    (hp2 : p ≤ 2 * h + 1 - μ.len) : optS h (μ, δ) p = (μ.addOne, δ) := by
  simp [optS, show ¬ p ≤ μ.len by omega, show p ≠ μ.len + 1 by omega, hp2]

/-- The addition positions of `optS` (**Part B, Setting**, of `q_oddbox_shapes.md`). -/
lemma optS_add (h : ℕ) (μ : Partition) (δ : Bool) {p : ℕ} (hp1 : μ.len + 1 < p)
    (hp2 : 2 * h + 1 - μ.len < p) : optS h (μ, δ) p = (μ.addE (2 * h + 2 - p), δ) := by
  simp [optS, show ¬ p ≤ μ.len by omega, show p ≠ μ.len + 1 by omega,
    show ¬ p ≤ 2 * h + 1 - μ.len by omega]

set_option maxHeartbeats 400000 in
/-- **Theorem L, (E)** of `q_oddbox_layers.md`: let `Λ` be an interlaced pair of level `m`,
`(ν, δ) ∈ Sh_{m−1}`, `1 ≤ j ≤ ℓ(ν)` and `ν' := ν − e_j`. If `1 ≤ p ≤ 2h + 1` and
`optS_p(ν, δ) ∈ Λ`, then there is `p'` with `p ≤ p' ≤ 2h + 1` and `optS_{p'}(ν', 1 − δ) ∈ Λ`.
(Only (D2) and `ℓ(ν) ≤ h` are used.) -/
theorem exchange {h m : ℕ} {Λ : Set Shape} (hΛ : IsInterlaced h m Λ) {ν : Partition}
    {δ : Bool} (hs : (ν, δ) ∈ Sh h (m - 1)) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ ν.len) {p : ℕ}
    (hp1 : 1 ≤ p) (hp : p ≤ 2 * h + 1) (hmem : optS h (ν, δ) p ∈ Λ) :
    ∃ p', p ≤ p' ∧ p' ≤ 2 * h + 1 ∧ optS h (ν.subE j, !δ) p' ∈ Λ := by
  have hℓh : ν.len ≤ h := hs.1
  set P := pm ν with hP
  clear_value P
  set a := ν.row j with ha_def
  clear_value a
  have ha : a ∈ P := by rw [hP, ha_def]; exact row_mem_parts ν hj1 hj
  have ha1 : 1 ≤ a := by rw [ha_def]; exact row_pos ν j hj1 hj
  have hca : 1 ≤ P.count a := Multiset.one_le_count_iff_mem.mpr ha
  have h0 : P.count 0 = 0 := by rw [hP]; exact count_zero_pm ν
  set ν' := ν.subE j with hν'_def
  clear_value ν'
  have hν' : pm ν' = (P.erase a + {a - 1}).filter (0 < ·)  := by
    rw [hν'_def, hP, ha_def]; exact pm_subE ν hj1 hj
  clear ha_def hν'_def
  have hc' : ∀ b, (pm ν').count b = if 0 < b then
      P.count b - (if b = a then 1 else 0) + (if b = a - 1 then 1 else 0) else 0 := by
    intro b; rw [hν', count_lower]
  have hpos : ∀ b ∈ P.erase a, 0 < b := fun b hb =>
    ν.pos b (by simpa [hP] using Multiset.mem_of_mem_erase hb)
  have hℓ' : ν'.len + (if a = 1 then 1 else 0) = ν.len := by
    have hP0 : 0 < Multiset.card P := Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩
    rw [len_eq_card, len_eq_card, hν', Multiset.filter_add, Multiset.filter_eq_self.mpr hpos,
      Multiset.card_add, Multiset.card_erase_of_mem ha, Multiset.filter_singleton]
    split_ifs <;> simp_all <;> omega
  have hℓ1 : 1 ≤ ν.len := le_trans hj1 hj
  have hL : (a ≠ 1 ∧ ν'.len = ν.len) ∨ (a = 1 ∧ ν'.len + 1 = ν.len) := by
    split_ifs at hℓ' with h1
    · exact Or.inr ⟨h1, hℓ'⟩
    · exact Or.inl ⟨h1, by omega⟩
  rcases Nat.lt_or_ge ν.len p with hpl | hpl
  · rcases Nat.lt_or_ge (ν.len + 1) p with hpl2 | hpl2
    · rcases Nat.lt_or_ge (2 * h + 1 - ν.len) p with hpl3 | hpl3
      · -- Case 4: an addition
        have hi1 : 1 ≤ 2 * h + 2 - p := by omega
        have hi2 : 2 * h + 2 - p ≤ ν.len := by omega
        rw [optS_add h ν δ hpl2 hpl3] at hmem
        set i := 2 * h + 2 - p with hi_def
        clear_value i
        set y := ν.row i with hy_def
        clear_value y
        have hy1 : 1 ≤ y := by rw [hy_def]; exact row_pos ν i hi1 hi2
        have hyP : y ∈ P := by rw [hP, hy_def]; exact row_mem_parts ν hi1 hi2
        have hcy := Multiset.one_le_count_iff_mem.mpr hyP
        have hκ : pm (ν.addE i) = (P.erase y + {y + 1}).filter (0 < ·)  := by
          rw [hP, hy_def]; exact pm_addE ν hi1 hi2
        have hirow := (le_cge_row ν hi1 hi2).2
        rw [← hy_def] at hirow
        clear hy_def
        by_cases h4 : y ≠ a ∨ 2 ≤ P.count a
        · -- 4a
          have haκ : a ∈ pm (ν.addE i) := by
            rw [mem_pm_iff, hκ, count_raise]; split_ifs <;> subst_vars <;> omega
          obtain ⟨κ', hκ', hmem'⟩ := lower_mem hΛ hmem haκ
          have hyν' : y ∈ pm ν' := by rw [mem_pm_iff, hc']; split_ifs <;> subst_vars <;> omega
          obtain ⟨hq1, hq2⟩ := row_cgt ν' hyν'
          refine ⟨2 * h + 2 - (cgt ν' y + 1), ?_, by omega, ?_⟩
          · have e := card_filter_lower P ha (y < ·) (fun b hb => by omega)
            rw [← hν'] at e
            unfold cgt at hirow hq1 ⊢
            split_ifs at e <;> subst_vars <;> omega
          · rw [optS_add h ν' (!δ) (by omega) (by omega),
              show 2 * h + 2 - (2 * h + 2 - (cgt ν' y + 1)) = cgt ν' y + 1 by omega]
            convert hmem' using 2
            apply eq_of_count; intro b
            simp only [pm_addE ν' (by omega) hq1, hq2, hκ', hκ, count_raise, count_lower, hc']
            rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
        · -- 4b
          push_neg at h4
          obtain ⟨hya, hca1⟩ := h4
          have hκ1 : y + 1 ∈ pm (ν.addE i) := by
            rw [mem_pm_iff, hκ, count_raise]; split_ifs <;> subst_vars <;> omega
          obtain ⟨κ', hκ', hmem'⟩ := lower_mem hΛ hmem hκ1
          have hκν : κ' = ν := by
            apply eq_of_count; intro b
            rw [hκ', count_lower, hκ, count_raise]; simp only [Nat.add_sub_cancel]
            rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
          rw [hκν] at hmem'
          clear hκν hκ'
          have hcge := cge_eq_cgt_add_count ν a
          by_cases ha2 : 2 ≤ a
          · have hmν' : a - 1 ∈ pm ν' := by rw [mem_pm_iff, hc']; split_ifs <;> subst_vars <;> omega
            obtain ⟨hq1, hq2⟩ := row_cgt ν' hmν'
            refine ⟨2 * h + 2 - (cgt ν' (a - 1) + 1), ?_, by omega, ?_⟩
            · have e := card_filter_lower P ha (a - 1 < ·) (fun b hb => by omega)
              rw [← hν'] at e
              have e2 : P.filter (a - 1 < ·) = P.filter (a ≤ ·) :=
                Multiset.filter_congr (fun b _ => by omega)
              rw [e2] at e
              simp only [show a - 1 < a by omega, show ¬ a - 1 < a - 1 by omega,
                if_true, if_false] at e
              unfold cgt at hirow hq1 ⊢
              unfold cge cgt at hcge
              subst hP hya
              omega
            · rw [optS_add h ν' (!δ) (by omega) (by omega),
                show 2 * h + 2 - (2 * h + 2 - (cgt ν' (a - 1) + 1)) = cgt ν' (a - 1) + 1 by omega]
              convert hmem' using 2
              apply eq_of_count; intro b
              simp only [pm_addE ν' (by omega) hq1, hq2, count_raise, hc']
              rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
          · have ha1' : a = 1 := by omega
            subst hya
            subst ha1'
            subst hP
            have hc1 := cge_one ν
            refine ⟨2 * h + 1 - ν'.len, by omega, by omega, ?_⟩
            rw [optS_mid h ν' (!δ) (by omega) le_rfl]
            convert hmem' using 2
            apply eq_of_count; intro b
            simp only [pm_addOne, count_addOne, hc']
            rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
      · -- Case 3: a middle position
        rw [optS_mid h ν δ hpl2 hpl3] at hmem
        have haκ : a ∈ pm ν.addOne := by
          rw [mem_pm_iff, pm_addOne, count_addOne]; split_ifs <;> subst_vars <;> omega
        obtain ⟨κ', hκ', hmem'⟩ := lower_mem hΛ hmem haκ
        refine ⟨2 * h + 1 - ν'.len, by omega, by omega, ?_⟩
        rw [optS_mid h ν' (!δ) (by omega) le_rfl]
        convert hmem' using 2
        apply eq_of_count; intro b
        simp only [pm_addOne, hκ', count_addOne, count_lower, hc']
        rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
    · -- Case 2: the switch of the mark, `p = ℓ + 1`
      have hpe : p = ν.len + 1 := by omega
      rw [hpe, optS_len_succ] at hmem
      by_cases ha2 : 2 ≤ a
      · have hmν' : a - 1 ∈ pm ν' := by rw [mem_pm_iff, hc']; split_ifs <;> subst_vars <;> omega
        obtain ⟨hq1, hq2, hq3⟩ := row_cge ν' hmν'
        refine ⟨2 * h + 2 - cge ν' (a - 1), by omega, by omega, ?_⟩
        rw [optS_add h ν' (!δ) (by omega) (by omega),
          show 2 * h + 2 - (2 * h + 2 - cge ν' (a - 1)) = cge ν' (a - 1) by omega]
        convert hmem using 2
        apply eq_of_count; intro b
        simp only [pm_addE ν' hq1 hq2, hq3, count_raise, hc']
        rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
      · refine ⟨ν.len + 1, by omega, by omega, ?_⟩
        rw [optS_mid h ν' (!δ) (by omega) (by omega)]
        convert hmem using 2
        apply eq_of_count; intro b
        simp only [pm_addOne, count_addOne, hc']
        rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega
  · -- Case 1: a removal
    rw [optS_rem h ν δ hpl] at hmem
    set x := ν.row p with hx_def
    clear_value x
    have hx1 : 1 ≤ x := by rw [hx_def]; exact row_pos ν p hp1 hpl
    have hxP : x ∈ P := by rw [hP, hx_def]; exact row_mem_parts ν hp1 hpl
    have hcx : 1 ≤ P.count x := Multiset.one_le_count_iff_mem.mpr hxP
    have hκ : pm (ν.subE p) = (P.erase x + {x - 1}).filter (0 < ·)  := by
      rw [hP, hx_def]; exact pm_subE ν hp1 hpl
    have hxrow := (le_cge_row ν hp1 hpl).1
    rw [← hx_def] at hxrow
    clear hx_def
    by_cases hxa : x = a
    · -- 1a
      have hκν : ν.subE p = ν' := by
        apply eq_of_count; intro b
        rw [hκ, hν', hxa]
      refine ⟨ν'.len + 1, by omega, by omega, ?_⟩
      rw [optS_len_succ, Bool.not_not, ← hκν]
      exact hmem
    · -- 1b
      have haκ : a ∈ pm (ν.subE p) := by
        rw [mem_pm_iff, hκ, count_lower]; split_ifs <;> subst_vars <;> omega
      obtain ⟨κ', hκ', hmem'⟩ := lower_mem hΛ hmem haκ
      have hxν' : x ∈ pm ν' := by rw [mem_pm_iff, hc']; split_ifs <;> subst_vars <;> omega
      obtain ⟨hq1, hq2, hq3⟩ := row_cge ν' hxν'
      refine ⟨cge ν' x, ?_, by omega, ?_⟩
      · have e := card_filter_lower P ha (x ≤ ·) (fun b hb => by omega)
        rw [← hν'] at e
        unfold cge at hxrow ⊢
        subst hP
        have hxa1 : (x ≤ a) = (x ≤ a - 1) := propext (by omega)
        simp only [hxa1] at e
        omega
      · rw [optS_rem h ν' (!δ) hq2]
        convert hmem' using 2
        apply eq_of_count; intro b
        rw [pm_subE ν' hq1 hq2, hq3, hκ', count_lower, count_lower, hκ, count_lower, hc']
        rcases Nat.eq_zero_or_pos b with rfl | hb0 <;> split_ifs <;> subst_vars <;> omega

/-- **Theorem L, (L2)** of `q_oddbox_layers.md`: let `m ≥ 1`, let `Λ` be an interlaced pair of
level `m`, `(ν, δ) ∈ Sh_{m−1}` and `1 ≤ j ≤ ℓ(ν)`. Then `F_Λ(ν, δ) ≤ F_Λ(ν − e_j, 1 − δ)`.
The proof is the one of the file: through (E) (`OddLayers.exchange`) and the chain (C2)
(`optS_filter_eq_Icc`) for the two shapes `(ν, δ)` and `(ν − e_j, 1 − δ)`. -/
theorem FS_le_FS_subE {h m : ℕ} (hm : 1 ≤ m) {Λ : Set Shape} (hΛ : IsInterlaced h m Λ)
    {ν : Partition} {δ : Bool} (hs : (ν, δ) ∈ Sh h (m - 1)) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ ν.len) : FS h Λ (ν, δ) ≤ FS h Λ (ν.subE j, !δ) := by
  classical
  have hs' := subE_mem_Sh hs hj1 hj
  have hC := Finset.ext_iff.mp (optS_filter_eq_Icc hm hΛ hs)
  have hC' := Finset.ext_iff.mp (optS_filter_eq_Icc hm hΛ hs')
  rcases Nat.eq_zero_or_pos (FS h Λ (ν, δ)) with h0 | hpos
  · omega
  · have hF := (hC (FS h Λ (ν, δ))).mpr (by simp only [Finset.mem_Icc]; omega)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hF
    obtain ⟨p', h1, h2, h3⟩ := exchange hΛ hs hj1 hj hF.1.1 hF.1.2 hF.2
    have hp' := (hC' p').mp
      (by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, h2⟩, h3⟩)
    simp only [Finset.mem_Icc] at hp'
    omega

end OddLayers
