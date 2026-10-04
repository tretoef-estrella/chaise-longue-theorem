module

public import RequestProject.OddShapes.Defs
public import RequestProject.Fibres.Main

/-!
# Auxiliary lemmas for Parts B and C of `q_oddbox_shapes.md`

* the non-zero elements of `T` with the restricted involution form a `Fibres.FibreSetting`
  (used to transfer part (ii) of `q_P1_fibres.md` in the proof of (B2));
* sizes and lengths of `μ − e_j`, `μ + e_j`, `μ ⊔ 1` (used in (B3) and (C1));
* the list `optS_p` through the list `opt_p` (used in (B2), (B5) and (C2));
* the two re-sorting facts used in the proof of (C2).
-/

@[expose] public section

namespace OddShapes

open ChainLemma ChainLemma.Partition Fibres Peel

variable {T : Type*} [Fintype T] [DecidableEq T] {h : ℕ}

namespace OddSetting

omit [DecidableEq T] in
/-- Helper for (B2) of `q_oddbox_shapes.md`: `−u ≠ 0` for `u ≠ 0`. -/
lemma neg_ne_zero (S : OddSetting T h) {u : T} (hu : u ≠ S.zero) : S.neg u ≠ S.zero := by
  intro e
  apply hu
  rw [← S.neg_neg u, e, S.neg_zero]

/-- Helper for (B2) of `q_oddbox_shapes.md`: `T ∖ {0}` with the restricted involution is a set
with `2h` elements and a fixed-point-free involution (the **Setting** of `q_P1_fibres.md`). -/
def sub (S : OddSetting T h) : FibreSetting {u : T // u ≠ S.zero} h where
  neg v := ⟨S.neg v.1, S.neg_ne_zero v.2⟩
  neg_neg v := Subtype.ext (S.neg_neg v.1)
  neg_ne v e := S.neg_ne v.1 v.2 (congrArg Subtype.val e)
  one_le := S.one_le
  card_eq := by
    rw [Fintype.card_subtype_compl, S.card_eq, Fintype.card_unique]
    omega

/-- Helper for (B1) and (B2) of `q_oddbox_shapes.md`: every tuple `M ∈ T^n` has a "non-zero part"
`N`, a tuple of non-zero elements with the same counts of the non-zero values; its length is
`n − #{i : M_i = 0}`. -/
lemma exists_subTuple (S : OddSetting T h) : ∀ (n : ℕ) (M : Fin n → T),
    ∃ (k : ℕ) (N : Fin k → {u : T // u ≠ S.zero}),
      (∀ v, cnt N v = cnt M v.1) ∧ k + cnt M S.zero = n
  | 0, M => ⟨0, Fin.elim0, fun v => by simp [cnt], by simp [cnt]⟩
  | n + 1, M => by
    obtain ⟨k, N, hN, hk⟩ := exists_subTuple S n (fun i : Fin n => M i.succ)
    have hM : M = consTuple (m := n + 1) (M 0) (fun i : Fin n => M i.succ) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [consTuple]
      | succ i => simp [consTuple]
    have hc : ∀ u, cnt M u = cnt (fun i : Fin n => M i.succ) u + if M 0 = u then 1 else 0 := by
      intro u
      conv_lhs => rw [hM]
      exact cnt_consTuple_succ _ _ u
    by_cases h0 : M 0 = S.zero
    · refine ⟨k, N, fun v => ?_, ?_⟩
      · rw [hc, hN, if_neg (by rw [h0]; exact fun e => v.2 e.symm)]; simp
      · rw [hc, if_pos h0]; omega
    · refine ⟨k + 1, consTuple (m := k + 1) ⟨M 0, h0⟩ N, fun v => ?_, ?_⟩
      · rw [hc, cnt_consTuple_succ, hN]
        congr 1
        simp [Subtype.ext_iff]
      · rw [hc, if_neg h0]; omega

/-- Helper for (B1) and (B2) of `q_oddbox_shapes.md`: `T` is `0` together with the non-zero
elements. -/
lemma univ_val_eq (S : OddSetting T h) :
    (Finset.univ : Finset T).val =
      S.zero ::ₘ (Finset.univ : Finset {u : T // u ≠ S.zero}).val.map Subtype.val := by
  apply (Multiset.Nodup.ext Finset.univ.nodup _).mpr
  · intro a
    by_cases ha : a = S.zero
    · simp [ha]
    · simp only [Finset.mem_val, Finset.mem_univ, Multiset.mem_cons, ha, Multiset.mem_map,
        true_and, Subtype.exists, false_or, true_iff]
      exact ⟨a, ha, rfl⟩
  · rw [Multiset.nodup_cons]
    refine ⟨by simp, Multiset.Nodup.map Subtype.val_injective Finset.univ.nodup⟩

/-- Helper for (B1) and (B2) of `q_oddbox_shapes.md`: the residue partition only involves the
counts of the non-zero values, so it is the residue partition (in the sense of
`q_P1_fibres.md`) of any tuple of non-zero elements with the same counts. -/
lemma resPart_eq_sub (S : OddSetting T h) {n k : ℕ} (M : Fin n → T)
    (N : Fin k → {u : T // u ≠ S.zero}) (hN : ∀ v, cnt N v = cnt M v.1) :
    S.resPart M = S.sub.resPart N := by
  unfold resPart FibreSetting.resPart
  apply ofMultiset_congr
  rw [univ_val_eq S, Multiset.map_cons, Multiset.filter_cons_of_neg _ (by simp [S.neg_zero]),
    Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro v _
  simp only [Function.comp, hN]
  rfl

end OddSetting

/-- Helper for (B1) of `q_oddbox_shapes.md`: the counts of a tuple `N ∈ T^k` add up to `k`. -/
lemma sum_cnt {U : Type*} [Fintype U] [DecidableEq U] {k : ℕ} (N : Fin k → U) :
    (Finset.univ.val.map (cnt N)).sum = k := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset U)) (f := N) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-- Helper for (B1) of `q_oddbox_shapes.md`: `|λ(N)| ≤ k` for a tuple `N` of length `k`
(in the setting of `q_P1_fibres.md`). -/
lemma size_resPart_le {U : Type*} [Fintype U] [DecidableEq U] (S : FibreSetting U h) {k : ℕ}
    (N : Fin k → U) : (S.resPart N).size ≤ k := by
  rw [FibreSetting.resPart, size_ofMultiset]
  calc _ ≤ (Finset.univ.val.map (cnt N)).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun u _ => Nat.sub_le _ _)
    _ = k := sum_cnt N

/-! ### Sizes and lengths of the options -/

/-- Helper for (B3), (C1) and (C2) of `q_oddbox_shapes.md`: rows `1 ≤ j ≤ ℓ` are parts. -/
lemma row_mem_parts (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    μ.row j ∈ (μ.parts : Multiset ℕ) := by
  have hi : j - 1 < μ.parts.length := by unfold Partition.len at hj; omega
  rw [row_eq_getElem μ j hi, Multiset.mem_coe]
  exact List.getElem_mem _

/-- Helper for (B3) and (C1) of `q_oddbox_shapes.md`: `ℓ` of `ofMultiset s`. -/
lemma len_ofMultiset (s : Multiset ℕ) : (ofMultiset s).len = (s.filter (0 < ·)).card := by
  rw [Partition.len, ← Multiset.coe_card, ofMultiset_parts]

/-- Helper for (B3) and (C1) of `q_oddbox_shapes.md`: `ℓ(μ − e_j) ≤ ℓ(μ)`. -/
lemma len_subE_le (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    (μ.subE j).len ≤ μ.len := by
  rw [subE_eq μ hj1 hj, len_ofMultiset]
  refine (Multiset.card_le_card (Multiset.filter_le _ _)).trans ?_
  rw [Multiset.card_add, Multiset.card_singleton,
    Multiset.card_erase_add_one (row_mem_parts μ hj1 hj), Multiset.coe_card]
  rfl

/-- Helper for (B3) of `q_oddbox_shapes.md`: `ℓ(μ + e_j) = ℓ(μ)`. -/
lemma len_addE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    (μ.addE j).len = μ.len := by
  rw [addE_eq μ hj1 hj, len_ofMultiset, Multiset.filter_eq_self.mpr]
  · rw [Multiset.card_add, Multiset.card_singleton,
      Multiset.card_erase_add_one (row_mem_parts μ hj1 hj), Multiset.coe_card]
    rfl
  · intro a ha
    rw [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with ha | ha
    · exact μ.pos a (by simpa using Multiset.mem_of_mem_erase ha)
    · omega

/-- Helper for (B3) and (C2) of `q_oddbox_shapes.md`: `ℓ(μ ⊔ 1) = ℓ(μ) + 1`. -/
lemma len_addOne (μ : Partition) : μ.addOne.len = μ.len + 1 := by
  simp [Partition.len, Partition.addOne]

/-- Helper for (B3) and (C1) of `q_oddbox_shapes.md`: `|μ − e_j| + 1 = |μ|`. -/
lemma size_subE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    (μ.subE j).size + 1 = μ.size := by
  rw [subE_eq μ hj1 hj]
  exact size_Gsub μ (row_mem_parts μ hj1 hj)

/-- Helper for (B3) of `q_oddbox_shapes.md`: `|μ + e_j| = |μ| + 1`. -/
lemma size_addE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    (μ.addE j).size = μ.size + 1 := by
  rw [addE_eq μ hj1 hj]
  exact size_Gadd μ (row_mem_parts μ hj1 hj)

/-! ### The list `optS_p` through the list `opt_p` -/

/-- **Part B, Setting** ("The list of options of a shape") of `q_oddbox_shapes.md`:
`optS_p(μ, δ) = (opt_p(μ), δ)` for `p ≤ ℓ` (with `L = 2h`). -/
lemma optS_of_le (h : ℕ) (μ : Partition) (δ : Bool) {p : ℕ} (hp : p ≤ μ.len) :
    optS h (μ, δ) p = (μ.opt (2 * h) p, δ) := by
  simp [optS, Partition.opt, hp]

/-- **Part B, Setting** ("The list of options of a shape") of `q_oddbox_shapes.md`:
`optS_{ℓ+1}(μ, δ) = (μ, 1 − δ)`. -/
lemma optS_len_succ (h : ℕ) (μ : Partition) (δ : Bool) :
    optS h (μ, δ) (μ.len + 1) = (μ, !δ) := by
  simp [optS]

/-- **Part B, Setting** ("The list of options of a shape") of `q_oddbox_shapes.md`:
`optS_p(μ, δ) = (opt_{p−1}(μ), δ)` for `p ≥ ℓ + 2` (with `L = 2h`). -/
lemma optS_of_ge (h : ℕ) (μ : Partition) (δ : Bool) {p : ℕ} (hp : μ.len + 2 ≤ p) :
    optS h (μ, δ) p = (μ.opt (2 * h) (p - 1), δ) := by
  unfold optS Partition.opt
  simp only [show ¬ p ≤ μ.len by omega, show p ≠ μ.len + 1 by omega,
    show ¬ p - 1 ≤ μ.len by omega, if_false]
  by_cases h1 : p ≤ 2 * h + 1 - μ.len
  · simp [h1, show p - 1 ≤ 2 * h - μ.len by omega]
  · simp [h1, show ¬ p - 1 ≤ 2 * h - μ.len by omega, show 2 * h + 1 - (p - 1) = 2 * h + 2 - p by omega]

/-- Helper for (B2) and (B5) of `q_oddbox_shapes.md`: as multisets,
`{optS_p(μ, δ) : p = 1, …, 2h + 1} = {(μ, 1 − δ)} + {(opt_p(μ), δ) : p = 1, …, 2h}`
(for `ℓ(μ) ≤ 2h`). -/
lemma map_optS (h : ℕ) (μ : Partition) (δ : Bool) (hℓ : μ.len ≤ 2 * h) :
    (Finset.Icc 1 (2 * h + 1)).val.map (optS h (μ, δ)) =
      (μ, !δ) ::ₘ (Finset.Icc 1 (2 * h)).val.map (fun p => (μ.opt (2 * h) p, δ)) := by
  set ℓ := μ.len with hℓdef
  let g : ℕ → ℕ := fun p => if p ≤ ℓ then p else p + 1
  have himg : ((Finset.Icc 1 (2 * h)).image g) = (Finset.Icc 1 (2 * h + 1)).erase (ℓ + 1) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_erase, g]
    constructor
    · rintro ⟨p, hp, rfl⟩
      split_ifs <;> omega
    · intro hx
      by_cases hxl : x ≤ ℓ
      · exact ⟨x, by omega, by simp [hxl]⟩
      · exact ⟨x - 1, by omega, by rw [if_neg (by omega)]; omega⟩
  have hinj : Set.InjOn g (Finset.Icc 1 (2 * h) : Set ℕ) := by
    intro a _ b _ hab
    simp only [g] at hab
    split_ifs at hab <;> omega
  have hval : (Finset.Icc 1 (2 * h + 1)).val =
      (ℓ + 1) ::ₘ (Finset.Icc 1 (2 * h)).val.map g := by
    rw [← Finset.image_val_of_injOn hinj, himg, Finset.erase_val, Multiset.cons_erase]
    rw [Finset.mem_val, Finset.mem_Icc]
    omega
  rw [hval, Multiset.map_cons, Multiset.map_map, hℓdef, optS_len_succ]
  congr 1
  apply Multiset.map_congr rfl
  intro p hp
  rw [Finset.mem_val, Finset.mem_Icc] at hp
  simp only [Function.comp, g]
  split_ifs with hpl
  · exact optS_of_le h μ δ hpl
  · rw [optS_of_ge h μ δ (by omega), Nat.add_sub_cancel]

/-! ### The two re-sorting facts used in the proof of (C2) -/

/-- Re-sorting fact for the proof of (C2) of `q_oddbox_shapes.md`:
`(μ ⊔ 1) − e_{ℓ+1} = μ`. -/
lemma addOne_subE (μ : Partition) : μ.addOne.subE (μ.len + 1) = μ := by
  have hrow : μ.addOne.row (μ.len + 1) = 1 := by
    simp [Partition.row, Partition.addOne, Partition.len]
  rw [subE_eq μ.addOne (by omega) (by rw [len_addOne]), hrow, addOne_eq, ofMultiset_parts,
    Multiset.filter_eq_self.mpr]
  · conv_rhs => rw [Fibres.Partition.eq_ofMultiset μ]
    apply ofMultiset_congr
    rw [add_comm (μ.parts : Multiset ℕ), Multiset.singleton_add, Multiset.erase_cons_head]
    simp
  · intro a ha
    rw [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with ha | ha
    · exact μ.pos a (by simpa using ha)
    · omega

/-- Re-sorting fact for the proof of (C2) of `q_oddbox_shapes.md`: for `1 ≤ j ≤ ℓ(μ)` there is a
row `j'` of `μ + e_j` (namely a row equal to `μ_j + 1`, e.g. the first row of `μ` of the same
length as row `j`) with `(μ + e_j) − e_{j'} = μ`. -/
lemma exists_addE_subE (μ : Partition) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ μ.len) :
    ∃ j', 1 ≤ j' ∧ j' ≤ (μ.addE j).len ∧ (μ.addE j).subE j' = μ := by
  set x := μ.row j with hx
  have hpos : ∀ a ∈ (μ.parts : Multiset ℕ).erase x + {x + 1}, 0 < a := by
    intro a ha
    rw [Multiset.mem_add, Multiset.mem_singleton] at ha
    rcases ha with ha | ha
    · exact μ.pos a (by simpa using Multiset.mem_of_mem_erase ha)
    · omega
  have hparts : ((μ.addE j).parts : Multiset ℕ) = (μ.parts : Multiset ℕ).erase x + {x + 1} := by
    rw [addE_eq μ hj1 hj, ofMultiset_parts, Multiset.filter_eq_self.mpr hpos]
  have hmem : x + 1 ∈ (μ.addE j).parts := by
    rw [← Multiset.mem_coe, hparts]
    simp
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hmem
  have hlen : i + 1 ≤ (μ.addE j).len := by unfold Partition.len; omega
  refine ⟨i + 1, by omega, hlen, ?_⟩
  have hrow : (μ.addE j).row (i + 1) = x + 1 := by
    rw [row_eq_getElem _ _ (by simpa using hi)]
    simpa using hix
  rw [subE_eq _ (by omega) hlen, hrow, hparts, Nat.add_sub_cancel]
  conv_rhs => rw [Fibres.Partition.eq_ofMultiset μ]
  apply ofMultiset_congr
  rw [add_comm _ {x + 1}, Multiset.singleton_add, Multiset.erase_cons_head, add_comm,
    Multiset.singleton_add, Multiset.cons_erase (row_mem_parts μ hj1 hj)]

end OddShapes
