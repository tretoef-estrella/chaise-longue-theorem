module

public import RequestProject.EvenColours.Points

/-!
# (C3) of `q_even_count_colours.md`: the closed forms of the block counts

* (a) `EvenColours.C3_a`: if `p ≠ 2`, `NS S 1 a` is the number of closed tuples of the standard
  point set `{1, …, (q − 1)/2} × {±1}`;
* (b) `EvenColours.C3_b`: if `p = 2`, `NS S 1 0 = 1` and `NS S 1 (2k' + 2) = Q^e_{k'}(q)`;
* (c) `EvenColours.C3_c`: if `−1 ≠ 1` in `F`, `NS S (−1) 0 = 1` and
  `NS S (−1) (2k' + 2) = Q^e_{k'}(q + 1)`;
* (d) `EvenColours.C3_d`: `NS S ζ a = 0` for odd `a`.
-/

@[expose] public section

namespace EvenColours

open ColSplit ColSurv ColComp Fibres TheoremB EvenBlocks

open scoped Classical

variable {F : Type*} [Field F] (S : ColSetting F)

/-- **(C3)** of `q_even_count_colours.md` (proof): `|{w : Om S // w ≠ 0}| = q − 1`. -/
theorem card_W : Fintype.card {w : Om S // w ≠ 0} = S.q - 1 := by
  rw [Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]

/-- **(C3)** of `q_even_count_colours.md` (proof): for a pointed point set `P`, `closedT P.neg n`
is the set of closed tuples of `P` (the only fixed point is `P.o`). -/
theorem closedT_eq_closedPointed_of {X : Type*} [Fintype X] [DecidableEq X] {h : ℕ}
    (P : EvenCount.PointedSetting X h) (n : ℕ) :
    closedT P.neg n = EvenCount.closedPointed P n := by
  ext g
  simp only [closedT, EvenCount.closedPointed, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro H
    exact H _ P.neg_o
  · intro H u hu
    rw [P.eq_o_of_neg_eq u hu]
    exact H

/-- **(C3)(a)** of `q_even_count_colours.md` (proof): if `p ≠ 2`, `{w : Om S // w ≠ 0}` with
`w ↦ −w` is a point set with a fixed-point-free involution and `q − 1 = 2·((q − 1)/2)` elements. -/
noncomputable def fibreW (hp : S.p ≠ 2) : FibreSetting {w : Om S // w ≠ 0} ((S.q - 1) / 2) where
  neg := negW S
  neg_neg := fun w => Subtype.ext (neg_neg w.1)
  neg_ne := fun w h => w.2 (eq_zero_of_neg_eq_self (ColOne.odd_q hp) (congrArg Subtype.val h))
  one_le := ColOne.one_le_h hp
  card_eq := by
    rw [card_W]
    obtain ⟨t, ht⟩ := ColOne.odd_q (S := S) hp
    omega

/-- **(C3)(a)** of `q_even_count_colours.md`: if `S.p ≠ 2`, then
`NS S 1 a = |closedTuples (stdSetting ((q − 1)/2) _) a|` (the count `N_1` of `ColCount`; there is
no fixed point). -/
theorem C3_a (hp : S.p ≠ 2) (a : ℕ) :
    NS S 1 a = (closedTuples (stdSetting ((S.q - 1) / 2) (ColOne.one_le_h hp)) a).card := by
  rw [NS, if_pos rfl]
  have hset : closedT (negW S) a = closedTuples (fibreW S hp) a := by
    ext g
    simp only [closedT, closedTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun H => H.1
    · exact fun H => ⟨H, fun u hu => absurd hu ((fibreW S hp).neg_ne u)⟩
  rw [hset]
  obtain ⟨e, he⟩ := exists_equiv_std (fibreW S hp)
  exact card_closedTuples_congr (fibreW S hp) _ e he a

/-- **(C3)(b)** of `q_even_count_colours.md` (proof): if `p = 2`, `{w : Om S // w ≠ 0}` with
`w ↦ −w` is a pointed point set, with the one fixed point `q/2` and `q − 1` elements. -/
noncomputable def pointedW (hp : S.p = 2) :
    EvenCount.PointedSetting {w : Om S // w ≠ 0} ((S.q - 2) / 2) where
  neg := negW S
  neg_neg := fun w => Subtype.ext (neg_neg w.1)
  o := ⟨halfQ S, halfQ_ne_zero S⟩
  neg_o := Subtype.ext ((neg_eq_self_iff_of_even (even_q_of_p_eq_two hp) _).2 (Or.inr rfl))
  eq_o_of_neg_eq := fun w h => Subtype.ext
    (((neg_eq_self_iff_of_even (even_q_of_p_eq_two hp) _).1 (congrArg Subtype.val h)).resolve_left
      w.2)
  card_eq := by
    rw [card_W]
    have := two_le_q S
    obtain ⟨t, ht⟩ := even_q_of_p_eq_two hp
    omega

/-- **(C3)(b)** of `q_even_count_colours.md`: if `S.p = 2`, then `NS S 1 0 = 1` and
`NS S 1 (2k' + 2) = Q^e_{k'}(q)`. -/
theorem C3_b (hp : S.p = 2) :
    NS S 1 0 = 1 ∧ ∀ k' : ℕ, NS S 1 (2 * k' + 2) = EvenCount.QkEven k' S.q := by
  refine ⟨by rw [NS, if_pos rfl, card_closedT_zero], fun k' => ?_⟩
  rw [NS, if_pos rfl]
  have hset : closedT (negW S) (2 * k' + 2) =
      EvenCount.closedPointed (pointedW S hp) (2 * k' + 2) :=
    closedT_eq_closedPointed_of (pointedW S hp) _
  rw [hset, EvenCount.card_closedPointed]
  congr 1
  have := two_le_q S
  obtain ⟨t, ht⟩ := even_q_of_p_eq_two hp
  omega

/-- **(C3)(c)** of `q_even_count_colours.md` (proof): if `−1 ≠ 1` in `F`, then `p ≠ 2`. -/
theorem p_ne_two_of_neg_one_ne_one (h : (-1 : F) ≠ 1) : S.p ≠ 2 := by
  intro hp
  haveI := S.charP
  have h2 : (2 : F) = 0 := by
    have := (CharP.cast_eq_zero_iff F S.p 2).2 (by rw [hp])
    exact_mod_cast this
  exact h (by linear_combination -h2)

/-- **(C3)(c)** of `q_even_count_colours.md` (proof): if `q` is odd, `Om S` with `w ↦ −w` is a
pointed point set, with the one fixed point `0` and `q = 2·((q − 1)/2) + 1` elements. -/
noncomputable def pointedOm (hq : Odd S.q) : EvenCount.PointedSetting (Om S) ((S.q - 1) / 2) where
  neg := fun w => -w
  neg_neg := neg_neg
  o := 0
  neg_o := neg_zero
  eq_o_of_neg_eq := fun _ h => eq_zero_of_neg_eq_self hq h
  card_eq := by
    rw [ZMod.card]
    obtain ⟨t, ht⟩ := hq
    omega

/-- **(C3)(c)** of `q_even_count_colours.md`: if `(−1 : F) ≠ 1`, then `NS S (−1) 0 = 1` and
`NS S (−1) (2k' + 2) = Q^e_{k'}(q + 1)` (here `q` is odd and the one fixed point is `0`). -/
theorem C3_c (h : (-1 : F) ≠ 1) :
    NS S (-1) 0 = 1 ∧ ∀ k' : ℕ, NS S (-1) (2 * k' + 2) = EvenCount.QkEven k' (S.q + 1) := by
  have hq := ColOne.odd_q (p_ne_two_of_neg_one_ne_one S h)
  refine ⟨by rw [NS, if_neg h, card_closedT_zero], fun k' => ?_⟩
  rw [NS, if_neg h]
  have hset : closedT (fun w : Om S => -w) (2 * k' + 2) =
      EvenCount.closedPointed (pointedOm S hq) (2 * k' + 2) :=
    closedT_eq_closedPointed_of (pointedOm S hq) _
  rw [hset, EvenCount.card_closedPointed]
  congr 1
  obtain ⟨t, ht⟩ := hq
  omega

/-- **(C3)(d)** of `q_even_count_colours.md`: for `a` odd, `NS S ζ a = 0`.  (Stated more
generally than in the file, for every colour `ζ : F`, not only for `ζ ∈ SInv S`: a closed tuple
always has even length.) -/
theorem C3_d (ζ : F) {a : ℕ} (ha : Odd a) : NS S ζ a = 0 := by
  have hnot : ¬ Even a := Nat.not_even_iff_odd.2 ha
  unfold NS
  split_ifs
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro g hg
    exact hnot (even_of_mem_closedT (fun w => Subtype.ext (neg_neg w.1)) hg)
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro g hg
    exact hnot (even_of_mem_closedT neg_neg hg)

end EvenColours

end
